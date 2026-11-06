From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_inflight_retry_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes and lists ---- *)

Lemma cir_map_inj : forall a b : list byte, map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] E; cbn [map] in E; try discriminate; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma cir_beq : forall a b, beq_bytes a b = true -> a = b.
Proof.
  intros a b. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)) as [E|E]; [|discriminate].
  intros _. apply cir_map_inj. exact E.
Qed.

Lemma cir_memcmp : forall n l r v, (n <= length l)%nat -> (n <= length r)%nat -> memcmp_model l r n = Some v ->
  (v = 0 <-> firstn n l = firstn n r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - cbn in Hm. injection Hm as <-. cbn [firstn]. split; [split; intros; reflexivity | lia].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn in Hl, Hr, Hm. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) Hm) as [[I1 I2] I3]. split; [|exact I3].
      assert (a = b) by (apply bv_eq; exact E). subst b. cbn [firstn]. split.
      * intros Hv. f_equal. tauto.
      * intros Q. injection Q as Q. tauto.
    + injection Hm as <-. split; [|lia]. cbn [firstn]. split.
      * intros. lia.
      * intros Q. injection Q as Q1 Q2. subst. lia.
Qed.

Lemma cir_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn.
  assert (Ln : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma cir_skipn_sub : forall (bs : list byte) k, (k <= length bs)%nat -> skipn k bs = sub bs (Z.of_nat k) (length bs - k).
Proof.
  intros bs k Hk. unfold sub. rewrite Nat2Z.id. symmetry. apply firstn_all2. rewrite length_skipn. lia.
Qed.

Lemma cir_rd : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

(* ---- comparisons of words ---- *)

Lemma cir_eqb0 : forall v, -256 < v < 256 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma cir_eqb0_s32 : forall v, -2^31 <= v < 2^31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma cir_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma cir_eqb : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma cir_swrap_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma cir_swrap_big : forall x, 2^31 <= x < 2^32 -> bv_swrap 32 x = x - 2^32.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (x + 2^31) with ((x + 2^31 - 2^32) + 1 * 2^32) by lia. rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma cir_wrap_neg : forall z, -2^63 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2^64.
Proof.
  intros z Hz. rewrite unsigned_lit_wrap. replace z with ((z + 2^64) + (-1) * 2^64) at 1 by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma cir_ltu_nl : forall z a, -2^63 <= z < 0 -> 0 <= a < 2^64 -> bv_ltu (Z_to_bv 64 z) (Z_to_bv 64 a) = (z + 2^64 <? a).
Proof. intros z a Hz Ha. unfold bv_ltu. rewrite (cir_wrap_neg z) by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma cir_ltu_nr : forall a z, 0 <= a < 2^64 -> -2^63 <= z < 0 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 z) = (a <? z + 2^64).
Proof. intros a z Ha Hz. unfold bv_ltu. rewrite (cir_wrap_neg z) by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma cir_land7 : forall t, 0 <= t < 2^64 -> t mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 7 = 0.
Proof. intros t Ht H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8. Qed.

(* addiw of the signed 32-bit retries and 1, against the 16-bit retry field *)
Lemma cir_addiw : forall u r, 0 <= u < 2^32 -> 0 <= r < 2^16 -> r = u32 (u + 1) ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) + 1))) (Z_to_bv 64 r) = true.
Proof.
  intros u r Hu Hr E. unfold u32 in E.
  destruct (Z.ltb_spec (u + 1) (2^32)) as [L|L].
  - rewrite Z.mod_small in E by lia. subst r.
    rewrite (cir_swrap_small u) by lia. rewrite unsigned_lit by lia. rewrite cir_swrap_small by lia.
    rewrite cir_eqb by lia. apply Z.eqb_refl.
  - assert (U : u = 2^32 - 1) by lia. subst u. replace ((2^32 - 1 + 1) mod 2^32) with 0 in E by reflexivity.
    subst r. vm_compute. reflexivity.
Qed.

(* bltu of the signed 32-bit max_retries and the 16-bit retry field *)
Lemma cir_ltu_max : forall x r, 0 <= x < 2^32 -> 0 <= r < 2^16 -> r <= x ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 r) = false.
Proof.
  intros x r Hx Hr Hle. destruct (Z.ltb_spec x (2^31)) as [L|L].
  - rewrite cir_swrap_small by lia. rewrite cir_ltu by lia. apply Z.ltb_ge. lia.
  - rewrite cir_swrap_big by lia. unfold bv_ltu. rewrite cir_wrap_neg by lia. rewrite unsigned_lit by lia.
    apply Z.ltb_ge. lia.
Qed.

(* ---- the model ---- *)

Lemma cir_model : forall B B' frame, check_inflight_retry_m B frame = Some (B', tt) ->
  B' = B /\ s32_at B 96 <> 0 /\ Z.of_nat (length frame) = u_at B 1640 8 /\ 28 <= Z.of_nat (length frame) /\
  120 + Z.of_nat (length frame) <= W_LEN /\
  firstn 26 frame = sub B 120 26 /\
  skipn 28 frame = sub B 148 (Z.to_nat (Z.of_nat (length frame) - 28)) /\
  sf_retry (rf frame) = u32 (u_at B 108 4 + 1) /\ sf_retry (rf frame) <= u_at B 65056 4 /\
  u64 (u_at B 65052 4 * 1000) <= u64 (u_at B 65000 8 - u_at B 112 8).
Proof.
  intros B B' frame H. unfold check_inflight_retry_m in H. cbv zeta in H.
  change (M_fly_on B) with (s32_at B 96) in H. change (M_fly_len B) with (u_at B 1640 8) in H.
  change (Z.to_nat RETRY_AT) with 26%nat in H. change (Z.to_nat (RETRY_AT + 2)) with 28%nat in H.
  change (A_M_fly_frame + RETRY_AT + 2) with 148 in H. change A_M_fly_frame with 120 in H.
  change (M_fly_retries B) with (u_at B 108 4) in H. change (Cfg_max_retries B) with (u_at B 65056 4) in H.
  change (g_now B) with (u_at B 65000 8) in H. change (M_fly_sent B) with (u_at B 112 8) in H.
  change (Cfg_ack_timeout_ms B) with (u_at B 65052 4) in H. unfold h_ms_m in H. unfold RETRY_AT in H.
  revert H.
  destruct (negb (truth (s32_at B 96)) || negb (Z.of_nat (length frame) =? u_at B 1640 8)
            || (Z.of_nat (length frame) <? 26 + 2)) eqn:C1; [intros H; discriminate H|].
  destruct (W_LEN <? 120 + Z.of_nat (length frame)) eqn:C2; [intros H; discriminate H|].
  destruct (negb (beq_bytes (firstn 26 frame) (sub B 120 26))
            || negb (beq_bytes (skipn 28 frame) (sub B 148 (Z.to_nat (Z.of_nat (length frame) - 26 - 2)))))
    eqn:C3; [intros H; discriminate H|].
  destruct (negb (sf_retry (rf frame) =? u32 (u_at B 108 4 + 1)) || (u_at B 65056 4 <? sf_retry (rf frame)))
    eqn:C4; [intros H; discriminate H|].
  destruct (u64 (u_at B 65000 8 - u_at B 112 8) <? u64 (u_at B 65052 4 * 1000)) eqn:C5;
    [intros H; discriminate H|].
  intros H. cbv iota in H. injection H; intros; subst B'.
  apply orb_false_iff in C1 as [C1 C1c]. apply orb_false_iff in C1 as [C1a C1b].
  apply negb_false_iff in C1a. apply negb_false_iff in C1b. unfold truth in C1a. apply negb_true_iff in C1a.
  apply Z.eqb_neq in C1a. apply Z.eqb_eq in C1b. apply Z.ltb_ge in C1c.
  apply Z.ltb_ge in C2.
  apply orb_false_iff in C3 as [C3a C3b]. apply negb_false_iff in C3a. apply negb_false_iff in C3b.
  apply cir_beq in C3a. apply cir_beq in C3b.
  apply orb_false_iff in C4 as [C4a C4b]. apply negb_false_iff in C4a. apply Z.eqb_eq in C4a.
  apply Z.ltb_ge in C4b. apply Z.ltb_ge in C5.
  replace (Z.of_nat (length frame) - 26 - 2) with (Z.of_nat (length frame) - 28) in C3b by lia.
  repeat split; try assumption; try reflexivity; lia.
Qed.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.
Ltac brf tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.

Theorem check_inflight_retry_holds : bcmp_contract -> check_inflight_retry_contract.
Proof.
  intros BC. unfold check_inflight_retry_contract, check_inflight_retry_ENTRY, check_inflight_retry_FRAME.
  unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' fa fp frame -> -> -> Hfa Hfa28 HFR OWF SFR OWP WM HM S16 ST LO WOS MI.
  unfold off_window in OWF, OWP. unfold w_off_stack in WOS.
  destruct SFR as (Hfp0 & Hfp8 & SB & HSB & LSB & SB0 & SB8 & SB16 & SB24 & SB26 & SB28 & SB30 & SB32 & SB36 & SB40
    & SB41 & SB48 & SB56 & SB64 & SB72).
  clear SB0 SB8 SB16 SB24 SB26 SB28 SB32 SB36 SB40 SB41 SB48 SB56 SB64 SB72.
  destruct (cir_model B B' frame HM) as (-> & HON & HLEN & H28 & HW & HEQ1 & HEQ2 & HRT & HMX & HTM).
  clear HM.
  set (len := Z.of_nat (length frame)) in *.
  assert (Elen : len = Z.of_nat (length frame)) by reflexivity.
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB.
  pose proof (bytes_at_bound rsegs m fa frame HFR) as FB.
  pose proof (bytes_at_bound rsegs m fp SB HSB) as PB. rewrite LSB in PB.
  pose proof (u_at_range SB 30 2) as R30. change (8 * Z.of_nat 2) with 16 in R30. rewrite SB30 in R30.
  pose proof (u_at_range B 108 4) as R108. change (8 * Z.of_nat 4) with 32 in R108.
  pose proof (u_at_range B 65056 4) as R65056. change (8 * Z.of_nat 4) with 32 in R65056.
  pose proof (u_at_range B 65052 4) as R65052. change (8 * Z.of_nat 4) with 32 in R65052.
  pose proof (u_at_range B 1640 8) as R1640. change (8 * Z.of_nat 8) with 64 in R1640.
  pose proof (u_at_range B 65000 8) as R65000. change (8 * Z.of_nat 8) with 64 in R65000.
  pose proof (u_at_range B 112 8) as R112. change (8 * Z.of_nat 8) with 64 in R112.
  pose proof (s32_range B 96) as R96.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts.
  (* the two bcmp calls: their results are 0 by the model *)
  assert (L26 : length (sub B 120 26) = 26%nat) by (apply length_sub; lia).
  destruct (memcmp_model_total frame (sub B 120 26) 26 ltac:(lia) ltac:(lia)) as [v1 Hv1].
  pose proof (cir_memcmp 26 frame (sub B 120 26) v1 ltac:(lia) ltac:(lia) Hv1) as [[V1a V1b] V1r].
  assert (V10 : v1 = 0) by (apply V1b; rewrite (@firstn_all2 byte 26 (sub B 120 26)) by lia; exact HEQ1).
  subst v1. clear V1a V1b V1r.
  assert (L2 : length (sub B 148 (Z.to_nat (len - 28))) = Z.to_nat (len - 28)) by (apply length_sub; lia).
  assert (LS : length (skipn 28 frame) = Z.to_nat (len - 28)) by (rewrite length_skipn; lia).
  destruct (memcmp_model_total (skipn 28 frame) (sub B 148 (Z.to_nat (len - 28))) (Z.to_nat (len - 28))
              ltac:(lia) ltac:(lia)) as [v2 Hv2].
  pose proof (cir_memcmp (Z.to_nat (len - 28)) (skipn 28 frame) (sub B 148 (Z.to_nat (len - 28))) v2
                ltac:(lia) ltac:(lia) Hv2) as [[V2a V2b] V2r].
  assert (V20 : v2 = 0) by (apply V2b; rewrite !firstn_all2 by lia; exact HEQ2).
  subst v2. clear V2a V2b V2r.
  carve_frame 48%nat ST.
  do 6 step.
  do 3 step.
  step.
  step.
  brf ltac:(rewrite cir_eqb0_s32 by lia; apply Z.eqb_neq; exact HON).
  do 2 step.
  step.
  brf ltac:(rewrite cir_ltu by lia; apply Z.ltb_ge; lia).
  step.
  step.
  brf ltac:(rewrite cir_eqb by lia; rewrite HLEN, Z.eqb_refl; reflexivity).
  do 5 step.
  (* bcmp (frame, M.fly.frame, 26) *)
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := frame) (rs := sub B 120 26) (v := 0);
      [ rewrite unsigned_lit by lia; exact HFR
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_UBSAN mm B 120 26); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv1
      | assumption ]
    | wk_post_call rsegs mm ].
  step.
  brf ltac:(reflexivity).
  (* ubsan: frame is not NULL and frame + RETRY_AT + 2 does not wrap (the traps at 0x15500-0x15514) *)
  step.
  brf ltac:(rewrite cir_eqb by lia; apply Z.eqb_neq; lia).
  do 2 step.
  brf ltac:(rewrite cir_ltu_nl by lia; apply Z.ltb_ge; lia).
  do 3 step.
  brf ltac:(rewrite cir_ltu_nr by lia; apply negb_false_iff, Z.ltb_lt; lia).
  do 4 step.
  (* bcmp (frame + 28, M.fly.frame + 28, len - 28) *)
  let mm := cur_mem in
  assert (HSK : bytes_at rsegs mm (fa + 28) (skipn 28 frame))
    by (rewrite (cir_skipn_sub frame 28) by lia;
        apply (cir_bytes_sub mm fa frame 28 (length frame - 28)); [exact HFR | lia | lia]).
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := skipn 28 frame) (rs := sub B 148 (Z.to_nat (len - 28))) (v := 0);
      [ rewrite unsigned_lit by lia; exact HSK
      | rewrite unsigned_lit by lia;
        apply (wm_src rsegs W_BASE_UBSAN mm B 148 (Z.to_nat (len - 28))); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv2
      | assumption ]
    | wk_post_call rsegs mm ].
  step.
  brf ltac:(reflexivity).
  (* ubsan: f is 8-aligned (the trap at 0x15530) *)
  step. step.
  brf ltac:(rewrite cir_land7 by (first [exact Hfp8 | lia]); reflexivity).
  (* f->retry = M.fly.retries + 1 *)
  step.
  let mm := cur_mem in pose proof (cir_rd mm fp SB 30 2 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD30.
  step.
  rewrite wm_lhu, SB30.
  step.
  step.
  brf ltac:(unfold s32_at; rewrite (cir_addiw (u_at B 108 4) (sf_retry (rf frame))) by (first [exact HRT | lia]);
            reflexivity).
  (* f->retry <= g_cfg.max_retries *)
  do 4 step.
  brf ltac:(unfold s32_at; apply cir_ltu_max; lia).
  (* g_now - M.fly.sent >= ms (g_cfg.ack_timeout_ms) *)
  do 7 step.
  brf ltac:(rewrite (unsigned_lit (u_at B 65000 8)), (unsigned_lit (u_at B 112 8)), (unsigned_lit (u_at B 65052 4))
              by lia;
            unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; exact HTM).
  (* the epilogue *)
  do 5 step.
  release_frame FR ST (bv_unsigned sp).
  do 2 step.
  apply evt_done. unfold QQ. do 15 eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [reflexivity | eassumption].
Qed.
