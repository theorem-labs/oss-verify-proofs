(* Proof of check_state_settle_contract_F (check_state_settle_F_c.v; image A, entry 0x85b34, frame 16 bytes), with
   StepF's step: every access side goal is closed from the rng fact of the accessed range.

   The walk (listing DgnTransportList.v, the 135 slots of the function, AF_check_state_settle = 0x48d0):
     0x85b34-0x85b38  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk. It is the only store.
     0x85b3c-0x85b48  a3 = GOT (0x5e52e0), a4 = OW (0x5f3060).
     0x85b4c-0x85b84  five pairs of lw at GOT + k and OW + k (k = 196 e2, 200 e3, 220 ndata, 208 desk, 212 foreign),
                      each pair followed by bne to the trap path 0x85d28.
     0x85b88-0x85b98  a0 = [0xa4090] = 0xac9f8; a1 = GOT.n; a6 = OW.n; a5 = [0xac9f8] = 0x7fff8000.
     0x85b9c          bne a1,a6 to 0x85bc0.
     0x85ba0-0x85bbc  (GOT.n = OW.n) a0 = g_s.state (0x5dfa30), a1 = M.state (0x5df16c); OW.n <= 0 goes to
                      0x85d24 (beq a0,a1 to the return 0x85d18, else the trap path); else a7 = (a0 = a1); j 0x85bc8.
     0x85bc0-0x85bc4  (GOT.n <> OW.n) a7 = 0; OW.n <= 0 goes to the trap path.
     0x85bc8-0x85bd8  a6 = min(OW.n, 16) (bltu), t1 = 0, t0 = 1.
     0x85bdc-0x85ca4  the loop, one iteration per state_settle_loop step, with t1 = 12 i and a6 = min(OW.n, 16) - i:
                      the 4-byte loads of GOT.t[i].state / old / reason and OW.t[i].state / old / reason, each after
                      the instrumented check of its address a (the signed shadow byte k at (a >> 3) + 0x7fff8000; when
                      k <> 0 the handlers at 0x85cac-0x85d04 test (a & 7) + 3 against k and come back to the load);
                      a7 &= (state and old equal) (0x85c1c bne to 0x85c58 when the states differ), t0 &= (reason
                      equal); a6 -= 1; t1 += 12; bne a6,zero back to 0x85bdc.
     0x85ca8          j 0x85d10.
     0x85d10-0x85d20  beq a7,zero and beq t0,zero go to the trap path; ld ra,8(sp); addi sp,sp,16; ret.

   How each check and branch is closed:
   - the six instrumented checks: the `addressable` premise of GOT.t[0..16) (or OW.t[0..16)) gives, for the checked
     address a of a 4-byte load inside it, its shadow byte k with k = 0 or (a mod 8) + 3 < k <= 7 (shadow_of_load).
     When k = 0 the bne falls through to the load; else the handler's bge to the report call (blt back to the load
     at 0x85d04) is decided by (a mod 8) + 3 < k, and the code comes back to the load. So no __asan_report_load4
     (0x85d0c, 0x85d30, 0x85d38, 0x85d3c, 0x85d44, 0x85d4c) is reached. The checked addresses lie in the arrays
     because the loop runs for i < min(OW.n, 16).
   - every load reads the world: tw_bytes_at of TWorldG turns tw_at into the bytes the load step reads, and
     lw_world names the loaded value as TWorld's accessor of Bw.
   - the trap path 0x85d28 / 0x85d2c (__asan_handle_no_return, abort): check_state_settle_m Bw = Some (Bw', tt) gives
     the five equalities, and state_settle_loop 16 Bw 0 ((GOT.n =? OW.n) && (g_s.state =? M.state)) true =
     (true, true). The loop invariant is the plain walk's (lib/Prog/T/check_state_settle.v): at iteration i,
     state_settle_loop (16 - i) Bw i s w = (true, true) with a7 = s and t0 = w; at the exit the loop has stopped,
     so a7 = t0 = 1. With OW.n <= 0 the loop does not run, so (GOT.n =? OW.n) && (g_s.state =? M.state) = true.
   - the world after: the run writes only its frame (munch), which the off_stk premise puts outside the hull
     [G_HARNESS_LO, G_HARNESS_HI) of the 18 payloads, so tw_at holds at the new memory with the same Bw
     (TMAP_A_kept), and the model gives Bw' = Bw.

   Templates: check_latest_drain_F.v (image A's F leaf form with a loop of instrumented world loads) and the plain
   walk lib/Prog/T/check_state_settle.v (the same model steps and the same loop invariant). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_state_settle_c check_state_settle_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ============================================================================
   The model: check_state_settle_m's facts
   ============================================================================ *)

Lemma css_model : forall B B', TC.check_state_settle_m B = Some (B', tt) ->
  B' = B /\ (TW.GOT_e2 B =? TW.OW_e2 B) = true /\ (TW.GOT_e3 B =? TW.OW_e3 B) = true /\
  (TW.GOT_ndata B =? TW.OW_ndata B) = true /\ (TW.GOT_desk B =? TW.OW_desk B) = true /\
  (TW.GOT_foreign B =? TW.OW_foreign B) = true /\
  TC.state_settle_loop (Z.to_nat TC.TRANS_MAX) B 0
    ((TW.GOT_n B =? TW.OW_n B) && (TW.S_state B =? TW.M_state B)) true = (true, true).
Proof.
  intros B B' H. unfold TC.check_state_settle_m in H.
  destruct (TW.GOT_e2 B =? TW.OW_e2 B) eqn:C1; cbn [negb orb] in H; [|discriminate H].
  destruct (TW.GOT_e3 B =? TW.OW_e3 B) eqn:C2; cbn [negb orb] in H; [|discriminate H].
  destruct (TW.GOT_ndata B =? TW.OW_ndata B) eqn:C3; cbn [negb orb] in H; [|discriminate H].
  destruct (TW.GOT_desk B =? TW.OW_desk B) eqn:C4; cbn [negb orb] in H; [|discriminate H].
  destruct (TW.GOT_foreign B =? TW.OW_foreign B) eqn:C5; cbn [negb orb] in H; [|discriminate H].
  destruct (TC.state_settle_loop (Z.to_nat TC.TRANS_MAX) B 0
              ((TW.GOT_n B =? TW.OW_n B) && (TW.S_state B =? TW.M_state B)) true) as [same why] eqn:LP.
  destruct same; cbn [negb] in H; [|discriminate H].
  destruct why; cbn [negb] in H; [|discriminate H].
  (* the world of the result, without injection on a world-carrying option *)
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H)
    as HB.
  cbv beta iota in HB.
  split; [symmetry; exact HB|]. repeat split; first [reflexivity | exact LP].
Qed.

(* one turn of the model's loop over the first min(OW.n, TRANS_MAX) transitions (fuzz_transport.c:718-721) *)
Lemma css_loop_step : forall B i s w, 0 <= i -> i < TW.OW_n B -> i < 16 ->
  TC.state_settle_loop (Z.to_nat (16 - i)) B i s w =
  TC.state_settle_loop (Z.to_nat (16 - (i + 1))) B (i + 1)
    (s && ((TW.GOT_t_state B i =? TW.OW_t_state B i) && (TW.GOT_t_old B i =? TW.OW_t_old B i)))
    (w && (TW.GOT_t_reason B i =? TW.OW_t_reason B i)).
Proof.
  intros B i s w H0 H1 H2.
  replace (Z.to_nat (16 - i)) with (S (Z.to_nat (16 - (i + 1)))) by lia.
  cbn [TC.state_settle_loop].
  replace ((i <? TW.OW_n B) && (i <? TC.TRANS_MAX)) with true
    by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; unfold TC.TRANS_MAX; lia).
  reflexivity.
Qed.

Lemma css_loop_stop : forall fuel B i s w, TW.OW_n B <= i \/ 16 <= i ->
  TC.state_settle_loop fuel B i s w = (s, w).
Proof.
  intros [|f] B i s w H; [reflexivity|]. cbn [TC.state_settle_loop].
  replace ((i <? TW.OW_n B) && (i <? TC.TRANS_MAX)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. unfold TC.TRANS_MAX. destruct H; [left|right]; apply Z.ltb_ge; lia.
Qed.

(* ============================================================================
   The world at the machine's view, and what survives the frame store
   ============================================================================ *)

(* a load of c bytes at b + k inside ONE payload, in the form the kit's load step reads *)
Lemma css_rd : forall (m : word -> option byte) Bw o b n k (c : nat),
  tw_at TMAP_A (csw_view m) Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat c <= n ->
  ov_read_bytes rsegs m (wa (b + k)) c = Some (TW.sub Bw (o + k) c).
Proof.
  intros m Bw o b n k c HW Hin Hk Hkc.
  pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  pose proof (tw_bytes_at rsegs m TMAP_A Bw o b n k c TMAP_A_ok HW Hin Hk Hkc) as BF.
  assert (LB : Z.of_nat (length Bw) = TW.W_LEN).
  { rewrite (tw_len TMAP_A _ Bw HW). apply Z2Nat.id. unfold TW.W_LEN. lia. }
  assert (L : length (TW.sub Bw (o + k) c) = c) by (apply TWorldLemmas.length_sub; lia).
  replace (wa (b + k)) with (wa (b + k + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (b + k) _ 0 c BF ltac:(lia)) by (rewrite L; lia).
  cbn [Z.to_nat skipn]. f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* the frame store keeps the world: the frame is outside the hull of the 18 payloads *)
Lemma css_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) -> tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *.
  exact (TMAP_A_kept m m' lo hi Bw H MU D).
Qed.

(* the frame store keeps `addressable`: a shadow byte of application memory is not in the frame, because both
   ends of the frame are application memory and shadow memory is not *)
Lemma css_addr_tp : forall (m m' : word -> option byte) (sp p n : Z),
  addressable m p n -> munch [(sp - 16, sp)] m m' -> app_mem (sp - 16) -> app_mem (sp - 1) ->
  addressable m' p n.
Proof.
  intros m m' sp p n (HP & HN & HE & AB) MU A1 A2.
  split; [exact HP|]. split; [exact HN|]. split; [exact HE|].
  intros i Hi. destruct (AB i Hi) as (APP & k & MK & SK).
  split; [exact APP|]. exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK |- *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP, A1, A2.
  eapply mrd_tp; [exact MU | | | exact MK].
  - destruct APP as [APP|APP]; Z.div_mod_to_equations; lia.
  - destruct APP as [APP|APP]; destruct A1 as [A1|A1]; destruct A2 as [A2|A2];
      Z.div_mod_to_equations; lia.
Qed.

(* ============================================================================
   What `addressable` gives for the shadow check of one load (fuzz_decode's image-A lemma)
   ============================================================================ *)

(* The check of a w-byte load at A + o reads the shadow byte of A + o and compares it with (A + o) mod 8 + (w - 1).
   The byte at A + o + min (w - 1) (7 - (A + o) mod 8) lies in the load and in the granule of A + o, so that
   shadow byte is either 0 or above (A + o) mod 8 + (w - 1). *)
Lemma shadow_of_load : forall (m : word -> option byte) (A n o w : Z),
  addressable m A n -> 0 <= o -> 0 < w -> o + w <= n ->
  exists k : byte,
    mrd rsegs m (wa ((A + o) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ ((A + o) mod 8 + (w - 1) < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m A n o w (HA & HN & HE & AB) Ho Hw Hon.
  pose proof (Z.mod_pos_bound (A + o) 8 ltac:(lia)) as MB.
  destruct (Z_le_dec ((A + o) mod 8 + (w - 1)) 7) as [LE|GT].
  - destruct (AB (o + (w - 1)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (w - 1))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (w - 1))) mod 8 = (A + o) mod 8 + (w - 1)) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK | exact SK].
  - destruct (AB (o + (7 - (A + o) mod 8)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (7 - (A + o) mod 8))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (7 - (A + o) mod 8))) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK|].
    left. destruct SK as [K0|K]; [exact K0 | lia].
Qed.

(* the shadow byte of GOT.t + o lies in the shadow range of GOT.t[0..16) (the rng premise, 25 bytes from
   shadow_addr 0x5e52e4) *)
Lemma css_shg : forall RNG o, rng RNG 2148223580 25 -> 0 <= o < 192 ->
  rng RNG ((6181604 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148223580 25); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* the same for OW.t[0..16) (25 bytes from shadow_addr 0x5f3064) *)
Lemma css_sho : forall RNG o, rng RNG 2148230668 25 -> 0 <= o < 192 ->
  rng RNG ((6238308 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148230668 25); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* ============================================================================
   The machine words of the comparisons (the plain walk's lemmas)
   ============================================================================ *)

Lemma shr3 : forall z, Z.shiftr z 3 = z / 8.
Proof. intros z. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma css_eqb_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma css_lts0_s32 : forall a, -2^31 <= a < 2^31 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 a) = (0 <? a).
Proof.
  intros a Ha. rewrite bv_lts_zero_l, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 a).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec 0 a); destruct (Z.ltb_spec a (2^63)); try reflexivity; lia.
  - destruct (Z.eqb_spec a 0) as [->|NZ]; [reflexivity|].
    replace (a mod 2^64) with (a + 2^64).
    + destruct (Z.ltb_spec 0 (a + 2^64)); destruct (Z.ltb_spec (a + 2^64) (2^63)); try reflexivity; lia.
    + symmetry. rewrite <- (Z.mod_add a 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma css_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma css_eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma css_lxor_eqb0 : forall x y, (Z.lxor x y =? 0) = (x =? y).
Proof.
  intros x y. destruct (Z.eqb_spec x y) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.eqb_neq. intros E. apply NE. apply Z.lxor_eq_0_iff. exact E.
Qed.

Lemma css_u_eqb : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  (bv_unsigned (Z_to_bv 64 a) =? bv_unsigned (Z_to_bv 64 b)) = (a =? b).
Proof. intros a b Ha Hb. exact (css_eqb_s32 a b Ha Hb). Qed.

Lemma css_sltiu1 : forall x, 0 <= x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (Z.b2z (x =? 0)).
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by exact Hx. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia.
Qed.

Lemma css_seqz_xor : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) 1
  = Z_to_bv 64 (Z.b2z (a =? b)).
Proof.
  intros a b Ha Hb.
  rewrite css_sltiu1 by (apply zr_lxor; apply zr_word).
  rewrite css_lxor_eqb0, css_u_eqb by assumption. reflexivity.
Qed.

Lemma css_snez_xor : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))))
  = Z_to_bv 64 (Z.b2z (negb (a =? b))).
Proof.
  intros a b Ha Hb.
  assert (X : inr64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by (apply zr_lxor; apply zr_word).
  pose proof (css_lxor_eqb0 (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))) as E.
  rewrite css_u_eqb in E by assumption.
  unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia.
  rewrite (unsigned_lit (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by exact X.
  unfold inr64 in X.
  destruct (Z.eqb_spec a b) as [Eab|Eab].
  - subst b. rewrite Z.lxor_nilpotent. reflexivity.
  - try rewrite (proj2 (Z.eqb_neq a b) Eab) in E. apply Z.eqb_neq in E.
    replace (0 <? Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))) with true
      by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

Lemma css_addiw_m1 : forall c : bool,
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.b2z c)) + -1)) = Z_to_bv 64 (if c then 0 else -1).
Proof. intros [|]; reflexivity. Qed.

Lemma css_and_mask : forall c w : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (if c then 0 else -1))) (bv_unsigned (Z_to_bv 64 (Z.b2z w))))
  = Z_to_bv 64 (Z.b2z (w && negb c)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma css_and_b2z : forall x y : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z x))) (bv_unsigned (Z_to_bv 64 (Z.b2z y))))
  = Z_to_bv 64 (Z.b2z (y && x)).
Proof. intros [|] [|]; reflexivity. Qed.

(* `blt` / `bge` of a literal with a sign-extended shadow byte *)
Lemma lts_lit : forall (x : Z) (k : byte), -2^63 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma bv_wrap64_7 : bv_wrap 64 7 = 7.
Proof. reflexivity. Qed.

(* ============================================================================
   The run
   ============================================================================ *)

Theorem check_state_settle_holds_F : check_state_settle_contract_F.
Proof.
  unfold check_state_settle_contract_F, CHECK_STATE_SETTLE, CHECK_STATE_SETTLE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' HW HM ST HLO HOFF AP1 AP2 CELLS OG OC ADG ADO
    RFR RGOT RCELL RGRD RORD RSS RMS RSGT RSOT.
  (* the model: Bw' = Bw, the five equalities and the loop's result *)
  destruct (css_model Bw Bw' HM) as (-> & C1 & C2 & C3 & C4 & C5 & LP). clear HM.
  (* the ranges with numeral bases (solve_acc1 takes its closed-literal branch only then) *)
  destruct check_state_settle_addrs as (EG & EO & ERD & _ & EGT & EOT & ETL & _ & ESS & EMS).
  rewrite EG, ERD in RGRD. rewrite EO, ERD in RORD. rewrite ESS in RSS. rewrite EMS in RMS.
  rewrite EGT, ETL in ADG, RSGT. rewrite EOT, ETL in ADO, RSOT.
  assert (RSG : rng RNG 2148223580 25) by exact RSGT.
  assert (RSO : rng RNG 2148230668 25) by exact RSOT.
  clear RSGT RSOT EG EO ERD EGT EOT ETL ESS EMS.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL.
  (* the stack and the hull *)
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  unfold off_stk, GOT_CELL_K, CELL_K in OG, OC.
  (* the ranges of the world values the code compares *)
  pose proof (TWorldLemmas.s32_range Bw TW.A_GOT_n) as RGn.
  change (TW.s32_at Bw TW.A_GOT_n) with (TW.GOT_n Bw) in RGn.
  pose proof (TWorldLemmas.s32_range Bw TW.A_OW_n) as ROn.
  change (TW.s32_at Bw TW.A_OW_n) with (TW.OW_n Bw) in ROn.
  (* the frame *)
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  (* 0x85b34-0x85b38: the frame and the store of ra *)
  step. step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -16) ?cs |- _ =>
    set (FRC := cs) in H; rename H into FR end.
  (* the world, the two arrays' shadow and the two runtime cells, after the only store *)
  assert (HWF : tw_at TMAP_A (csw_view mF) Bw).
  { apply (css_kept m mF (bv_unsigned sp - 16) (bv_unsigned sp) Bw HW MU).
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia. }
  pose proof (css_addr_tp m mF (bv_unsigned sp) 6181604 192 ADG MU AP1 AP2) as ADGF.
  pose proof (css_addr_tp m mF (bv_unsigned sp) 6238308 192 ADO MU AP1 AP2) as ADOF.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (CK0 : bytes_at rsegs mF 707064 (le8 (wa 2147450880)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact CK]).
  assert (GCK0 : bytes_at rsegs mF 671888 (le8 (wa 707064)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact GCK]).
  clear CK GCK CELLS ADG ADO.
  (* ---- the return, 0x85d18 ---- *)
  assert (EPI : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 : word),
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x85d18) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30.
    unfold FRC in FR.
    step.
    release_frame FR ST (bv_unsigned sp).
    step. step.
    apply evtF_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact ST|]. split; [reflexivity | exact HWF]. }
  (* ---- the loop, 0x85bdc: iteration i of cnt = min(OW.n, 16), t1 = 12 i, a6 = cnt - i ---- *)
  assert (LOOP : forall (k : nat) (i cnt T1 N6 : Z) (s w : bool) (x7 x10 x11 x12 x28 x29 x30 : word),
    Z.of_nat k = cnt - i -> 0 <= i < cnt -> cnt = Z.min (TW.OW_n Bw) 16 ->
    T1 = 12 * i -> N6 = cnt - i ->
    TC.state_settle_loop (Z.to_nat (16 - i)) Bw i s w = (true, true) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1) x7 s0 s1
                x10 x11 x12 (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x85bdc) fc None mF (seg_rom rsegs))).
  { induction k as [|k IH]; intros i cnt T1 N6 s w x7 x10 x11 x12 x28 x29 x30 Hk Hi Hc HT HN HL; [lia|].
    rewrite css_loop_step in HL by lia.
    (* ---- 0x85c84: after the six checks; a0 = GOT.t[i].reason ---- *)
    assert (J7 : forall (AOB ARO : Z) (y7 y29 y30 : word),
      AOB = 6238312 + 12 * i -> ARO = 6238316 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1) y7 s0 s1
                  (Z_to_bv 64 (TW.GOT_t_reason Bw i)) (Z_to_bv 64 AOB) (Z_to_bv 64 ARO)
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 (Z.b2z ((TW.GOT_t_state Bw i =? TW.OW_t_state Bw i)
                                      && (TW.GOT_t_old Bw i =? TW.OW_t_old Bw i)))) y29 y30 t6)
            F (Z_to_bv 64 0x85c84) fc None mF (seg_rom rsegs))).
    { intros AOB ARO y7 y29 y30 HOB HRO.
      (* 0x85c84 lw a1,4(a1): OW.t[i].reason *)
      pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW (12 + 12 * i) 4 HWF TMAP_A_OW ltac:(lia)
        ltac:(unfold TW.SZ_OW; lia)) as RD.
      unfold TA_OW in RD.
      replace (TW.OFF_OW + (12 + 12 * i)) with (TW.A_OW_t_reason i) in RD by (unfold TW.A_OW_t_reason; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_OW_t_reason i)) with (TW.OW_t_reason Bw i). clear RD.
      (* 0x85c88 and a7,t3,a7: a7 = s && (state and old equal) *)
      step. rewrite css_and_b2z.
      (* 0x85c8c addi a6,a6,-1 *)
      step.
      (* 0x85c90-0x85c9c: a0 = (reason unequal) - 1; t0 = a0 & t0 = w && (reason equal) *)
      step. step. rewrite css_snez_xor by (apply TWorldLemmas.s32_range).
      step. rewrite css_addiw_m1.
      step. rewrite css_and_mask, negb_involutive.
      (* 0x85ca0 addi t1,t1,12 *)
      step.
      (* 0x85ca4 bne a6,zero *)
      step.
      rewrite (css_eqb_lit (N6 + -1) 0) by lia.
      destruct (Z.eqb_spec (N6 + -1) 0) as [E0|E0]; cbn [negb]; cbv iota.
      - (* the last iteration: the loop has stopped with (true, true) *)
        rewrite css_loop_stop in HL by lia.
        injection HL as Hs Hw. rewrite Hs, Hw. cbn [Z.b2z].
        (* 0x85ca8 j 0x85d10; beq a7,zero; beq t0,zero *)
        step.
        step. try if_false.
        step. try if_false.
        apply EPI.
      - (* back to 0x85bdc with i + 1 *)
        apply (IH (i + 1) cnt); [lia | lia | exact Hc | lia | lia | exact HL]. }
    (* ---- 0x85c6c: after the check of GOT.t[i].reason; t3 = (state and old equal) ---- *)
    assert (J6 : forall (ARG AOB AO : Z) (y12 y29 y30 : word),
      ARG = 6181612 + 12 * i -> AOB = 6238312 + 12 * i -> AO = 6238304 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1)
                  (Z_to_bv 64 AO) s0 s1
                  (Z_to_bv 64 ARG) (Z_to_bv 64 AOB) y12
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 (Z.b2z ((TW.GOT_t_state Bw i =? TW.OW_t_state Bw i)
                                      && (TW.GOT_t_old Bw i =? TW.OW_t_old Bw i)))) y29 y30 t6)
            F (Z_to_bv 64 0x85c6c) fc None mF (seg_rom rsegs))).
    { intros ARG AOB AO y12 y29 y30 HRG HOB HO.
      (* the shadow byte of OW.t[i].reason *)
      destruct (shadow_of_load mF 6238308 192 (12 * i + 8) 4 ADOF ltac:(lia) ltac:(lia) ltac:(lia))
        as (k6 & MK6 & SK6).
      replace (6238308 + (12 * i + 8)) with (AO + 12) in MK6, SK6 by lia.
      change (4 - 1) with 3 in SK6.
      pose proof (css_sho RNG (12 * i + 8) RSO ltac:(lia)) as RK6.
      replace (6238308 + (12 * i + 8)) with (AO + 12) in RK6 by lia.
      unfold ASAN_K in MK6, RK6.
      pose proof (rd1 mF _ _ MK6) as RDk6.
      (* 0x85c6c-0x85c78: a2 = OW + 12 i + 12; t2 = its shadow byte *)
      step.
      step. rewrite (unsigned_lit (AO + 12)) by lia. rewrite shr3.
      step. step.
      (* 0x85c7c lw a0,0(a0): GOT.t[i].reason *)
      pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT (12 + 12 * i) 4 HWF TMAP_A_GOT ltac:(lia)
        ltac:(unfold TW.SZ_GOT; lia)) as RD.
      unfold TA_GOT in RD.
      replace (TW.OFF_GOT + (12 + 12 * i)) with (TW.A_GOT_t_reason i) in RD by (unfold TW.A_GOT_t_reason; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_GOT_t_reason i)) with (TW.GOT_t_reason Bw i). clear RD.
      (* 0x85c80 bne t2,zero *)
      step. rewrite sxb_eq0.
      destruct SK6 as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
        apply (J7 AOB (AO + 12)); lia.
      - rewrite (proj2 (Z.eqb_neq (bv_signed k6) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x85cdc-0x85ce8: the handler goes back to 0x85c84 *)
        step. step.
        step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit (AO + 12)) by lia.
        rewrite (lts_lit ((AO + 12) mod 8 + 3) k6 ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        step. apply (J7 AOB (AO + 12)); lia. }
    (* ---- 0x85c5c: the join of the state / old compare; t3 = st ---- *)
    assert (J5 : forall (st : bool) (ARG AOB AO : Z) (y12 y29 y30 : word),
      st = ((TW.GOT_t_state Bw i =? TW.OW_t_state Bw i) && (TW.GOT_t_old Bw i =? TW.OW_t_old Bw i)) ->
      ARG = 6181612 + 12 * i -> AOB = 6238312 + 12 * i -> AO = 6238304 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1)
                  (Z_to_bv 64 AO) s0 s1
                  (Z_to_bv 64 ARG) (Z_to_bv 64 AOB) y12
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 (Z.b2z st)) y29 y30 t6)
            F (Z_to_bv 64 0x85c5c) fc None mF (seg_rom rsegs))).
    { intros st ARG AOB AO y12 y29 y30 Hst HRG HOB HO. subst st.
      (* the shadow byte of GOT.t[i].reason *)
      destruct (shadow_of_load mF 6181604 192 (12 * i + 8) 4 ADGF ltac:(lia) ltac:(lia) ltac:(lia))
        as (k5 & MK5 & SK5).
      replace (6181604 + (12 * i + 8)) with ARG in MK5, SK5 by lia.
      change (4 - 1) with 3 in SK5.
      pose proof (css_shg RNG (12 * i + 8) RSG ltac:(lia)) as RK5.
      replace (6181604 + (12 * i + 8)) with ARG in RK5 by lia.
      unfold ASAN_K in MK5, RK5.
      pose proof (rd1 mF _ _ MK5) as RDk5.
      (* 0x85c5c-0x85c64: a2 = the shadow byte of a0 *)
      step. rewrite (unsigned_lit ARG) by lia. rewrite shr3.
      step. step.
      (* 0x85c68 bne a2,zero *)
      step. rewrite sxb_eq0.
      destruct SK5 as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
        apply (J6 ARG AOB AO); lia.
      - rewrite (proj2 (Z.eqb_neq (bv_signed k5) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x85ccc-0x85cd8: the handler goes back to 0x85c6c *)
        step. step.
        step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit ARG) by lia.
        rewrite (lts_lit (ARG mod 8 + 3) k5 ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        step. apply (J6 ARG AOB AO); lia. }
    (* ---- 0x85c48: the states are equal, after the check of OW.t[i].old; a2 = GOT.t[i].old ---- *)
    assert (J4 : forall (ARG AOB AO : Z) (y28 y29 y30 : word),
      (TW.GOT_t_state Bw i =? TW.OW_t_state Bw i) = true ->
      ARG = 6181612 + 12 * i -> AOB = 6238312 + 12 * i -> AO = 6238304 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1)
                  (Z_to_bv 64 AO) s0 s1
                  (Z_to_bv 64 ARG) (Z_to_bv 64 AOB) (Z_to_bv 64 (TW.GOT_t_old Bw i))
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 t6)
            F (Z_to_bv 64 0x85c48) fc None mF (seg_rom rsegs))).
    { intros ARG AOB AO y28 y29 y30 HEst HRG HOB HO.
      (* 0x85c48 lw t3,0(a1): OW.t[i].old *)
      pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW (8 + 12 * i) 4 HWF TMAP_A_OW ltac:(lia)
        ltac:(unfold TW.SZ_OW; lia)) as RD.
      unfold TA_OW in RD.
      replace (TW.OFF_OW + (8 + 12 * i)) with (TW.A_OW_t_old i) in RD by (unfold TW.A_OW_t_old; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_OW_t_old i)) with (TW.OW_t_old Bw i). clear RD.
      (* 0x85c4c-0x85c50: t3 = (GOT.t[i].old = OW.t[i].old) *)
      step. step. rewrite css_seqz_xor by (apply TWorldLemmas.s32_range).
      (* 0x85c54 j 0x85c5c *)
      step.
      apply (J5 (TW.GOT_t_old Bw i =? TW.OW_t_old Bw i) ARG AOB AO); [rewrite HEst; reflexivity | lia | lia | lia]. }
    (* ---- 0x85c34: the states are equal, after the check of GOT.t[i].old; a2 = GOT + 12 i + 8 ---- *)
    assert (J3 : forall (ARG AOB AGB AO : Z) (y28 y29 y30 : word),
      (TW.GOT_t_state Bw i =? TW.OW_t_state Bw i) = true ->
      ARG = 6181612 + 12 * i -> AOB = 6238312 + 12 * i -> AGB = 6181608 + 12 * i -> AO = 6238304 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1)
                  (Z_to_bv 64 AO) s0 s1
                  (Z_to_bv 64 ARG) (Z_to_bv 64 AOB) (Z_to_bv 64 AGB)
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 t6)
            F (Z_to_bv 64 0x85c34) fc None mF (seg_rom rsegs))).
    { intros ARG AOB AGB AO y28 y29 y30 HEst HRG HOB HGB HO.
      (* the shadow byte of OW.t[i].old *)
      destruct (shadow_of_load mF 6238308 192 (12 * i + 4) 4 ADOF ltac:(lia) ltac:(lia) ltac:(lia))
        as (k4 & MK4 & SK4).
      replace (6238308 + (12 * i + 4)) with AOB in MK4, SK4 by lia.
      change (4 - 1) with 3 in SK4.
      pose proof (css_sho RNG (12 * i + 4) RSO ltac:(lia)) as RK4.
      replace (6238308 + (12 * i + 4)) with AOB in RK4 by lia.
      unfold ASAN_K in MK4, RK4.
      pose proof (rd1 mF _ _ MK4) as RDk4.
      (* 0x85c34-0x85c3c: t3 = the shadow byte of a1 *)
      step. rewrite (unsigned_lit AOB) by lia. rewrite shr3.
      step. step.
      (* 0x85c40 lw a2,-4(a0): GOT.t[i].old *)
      pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT (8 + 12 * i) 4 HWF TMAP_A_GOT ltac:(lia)
        ltac:(unfold TW.SZ_GOT; lia)) as RD.
      unfold TA_GOT in RD.
      replace (TW.OFF_GOT + (8 + 12 * i)) with (TW.A_GOT_t_old i) in RD by (unfold TW.A_GOT_t_old; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_GOT_t_old i)) with (TW.GOT_t_old Bw i). clear RD.
      (* 0x85c44 bne t3,zero *)
      step. rewrite sxb_eq0.
      destruct SK4 as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
        apply (J4 ARG AOB AO); [exact HEst | lia | lia | lia].
      - rewrite (proj2 (Z.eqb_neq (bv_signed k4) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x85cfc-0x85d04: the handler's blt goes back to 0x85c48 *)
        step. step.
        step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit AOB) by lia.
        rewrite (lts_lit (AOB mod 8 + 3) k4 ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        apply (J4 ARG AOB AO); [exact HEst | lia | lia | lia]. }
    (* ---- 0x85c14: after the check of OW.t[i].state; t3 = GOT.t[i].state ---- *)
    assert (J2 : forall (AG ARG AO ASB : Z) (y29 y30 : word),
      AG = 6181600 + 12 * i -> ARG = 6181612 + 12 * i -> AO = 6238304 + 12 * i -> ASB = 6238308 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1)
                  (Z_to_bv 64 AO) s0 s1
                  (Z_to_bv 64 ARG) (Z_to_bv 64 ASB) (Z_to_bv 64 AG)
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 (TW.GOT_t_state Bw i)) y29 y30 t6)
            F (Z_to_bv 64 0x85c14) fc None mF (seg_rom rsegs))).
    { intros AG ARG AO ASB y29 y30 HG HRG HO HSB.
      (* 0x85c14 addi a1,t2,8; 0x85c18 lw t4,-4(a1): OW.t[i].state *)
      step.
      pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW (4 + 12 * i) 4 HWF TMAP_A_OW ltac:(lia)
        ltac:(unfold TW.SZ_OW; lia)) as RD.
      unfold TA_OW in RD.
      replace (TW.OFF_OW + (4 + 12 * i)) with (TW.A_OW_t_state i) in RD by (unfold TW.A_OW_t_state; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_OW_t_state i)) with (TW.OW_t_state Bw i). clear RD.
      (* 0x85c1c bne t3,t4 to 0x85c58 *)
      step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range).
      (* the destruct also turns the test in J3 .. J7 and HL into its value *)
      destruct (Z.eqb_spec (TW.GOT_t_state Bw i) (TW.OW_t_state Bw i)) as [Est|Est]; cbn [negb]; cbv iota.
      - (* the states are equal: 0x85c20 addi a2,a2,8 and the check of GOT.t[i].old *)
        step.
        destruct (shadow_of_load mF 6181604 192 (12 * i + 4) 4 ADGF ltac:(lia) ltac:(lia) ltac:(lia))
          as (k3 & MK3 & SK3).
        replace (6181604 + (12 * i + 4)) with (AG + 8) in MK3, SK3 by lia.
        change (4 - 1) with 3 in SK3.
        pose proof (css_shg RNG (12 * i + 4) RSG ltac:(lia)) as RK3.
        replace (6181604 + (12 * i + 4)) with (AG + 8) in RK3 by lia.
        unfold ASAN_K in MK3, RK3.
        pose proof (rd1 mF _ _ MK3) as RDk3.
        (* 0x85c24-0x85c2c: t3 = the shadow byte of a2 *)
        step. rewrite (unsigned_lit (AG + 8)) by lia. rewrite shr3.
        step. step.
        (* 0x85c30 bne t3,zero *)
        step. rewrite sxb_eq0.
        destruct SK3 as [C|[C Cu]].
        + rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
          apply (J3 ARG (AO + 8) (AG + 8) AO); [reflexivity | lia | lia | lia | lia].
        + rewrite (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)). cbn [negb]. cbv iota.
          (* 0x85cec-0x85cf8: the handler goes back to 0x85c34 *)
          step. step.
          step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit (AG + 8)) by lia.
          rewrite (lts_lit ((AG + 8) mod 8 + 3) k3 ltac:(lia)).
          rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
          step. apply (J3 ARG (AO + 8) (AG + 8) AO); [reflexivity | lia | lia | lia | lia].
      - (* the states differ: 0x85c58 t3 = 0 *)
        step.
        apply (J5 false ARG (AO + 8) AO); [reflexivity | lia | lia | lia]. }
    (* ---- 0x85bf4: after the check of GOT.t[i].state; a0 = GOT + 12 i + 4, a2 = GOT + 12 i ---- *)
    assert (J1 : forall (AG AS : Z) (y7 y11 : word),
      AG = 6181600 + 12 * i -> AS = 6181604 + 12 * i ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 T1) y7 s0 s1
                  (Z_to_bv 64 AS) y11 (Z_to_bv 64 AG)
                  (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880) (Z_to_bv 64 N6)
                  (Z_to_bv 64 (Z.b2z s)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x85bf4) fc None mF (seg_rom rsegs))).
    { intros AG AS y7 y11 HG HS.
      (* 0x85bf4-0x85bfc: a0 = GOT + 12 i + 12; t2 = OW + 12 i; a1 = OW + 12 i + 4 *)
      step. step. step.
      (* the shadow byte of OW.t[i].state *)
      destruct (shadow_of_load mF 6238308 192 (12 * i) 4 ADOF ltac:(lia) ltac:(lia) ltac:(lia))
        as (k2 & MK2 & SK2).
      replace (6238308 + 12 * i) with (T1 + 6238308) in MK2, SK2 by lia.
      change (4 - 1) with 3 in SK2.
      pose proof (css_sho RNG (12 * i) RSO ltac:(lia)) as RK2.
      replace (6238308 + 12 * i) with (T1 + 6238308) in RK2 by lia.
      unfold ASAN_K in MK2, RK2.
      pose proof (rd1 mF _ _ MK2) as RDk2.
      (* 0x85c00-0x85c08: t4 = the shadow byte of a1 *)
      step. rewrite (unsigned_lit (T1 + 6238308)) by lia. rewrite shr3.
      step. step.
      (* 0x85c0c lw t3,-8(a0): GOT.t[i].state *)
      pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT (4 + 12 * i) 4 HWF TMAP_A_GOT ltac:(lia)
        ltac:(unfold TW.SZ_GOT; lia)) as RD.
      unfold TA_GOT in RD.
      replace (TW.OFF_GOT + (4 + 12 * i)) with (TW.A_GOT_t_state i) in RD by (unfold TW.A_GOT_t_state; lia).
      step. rewrite lw_world. change (TW.s32_at Bw (TW.A_GOT_t_state i)) with (TW.GOT_t_state Bw i). clear RD.
      (* 0x85c10 bne t4,zero *)
      step. rewrite sxb_eq0.
      destruct SK2 as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
        apply (J2 AG (AG + 12) (T1 + 6238304) (T1 + 6238308)); lia.
      - rewrite (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x85cbc-0x85cc8: the handler goes back to 0x85c14 *)
        step. step.
        step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit (T1 + 6238308)) by lia.
        rewrite (lts_lit ((T1 + 6238308) mod 8 + 3) k2 ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        step. apply (J2 AG (AG + 12) (T1 + 6238304) (T1 + 6238308)); lia. }
    (* ---- 0x85bdc-0x85bf0: a2 = GOT + 12 i; a0 = a2 + 4; the check of GOT.t[i].state ---- *)
    step. step.
    destruct (shadow_of_load mF 6181604 192 (12 * i) 4 ADGF ltac:(lia) ltac:(lia) ltac:(lia))
      as (k1 & MK1 & SK1).
    replace (6181604 + 12 * i) with (T1 + 6181604) in MK1, SK1 by lia.
    change (4 - 1) with 3 in SK1.
    pose proof (css_shg RNG (12 * i) RSG ltac:(lia)) as RK1.
    replace (6181604 + 12 * i) with (T1 + 6181604) in RK1 by lia.
    unfold ASAN_K in MK1, RK1.
    pose proof (rd1 mF _ _ MK1) as RDk1.
    step. rewrite (unsigned_lit (T1 + 6181604)) by lia. rewrite shr3.
    step. step.
    (* 0x85bf0 bne a1,zero *)
    step. rewrite sxb_eq0.
    destruct SK1 as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota.
      apply (J1 (T1 + 6181600) (T1 + 6181604)); lia.
    - rewrite (proj2 (Z.eqb_neq (bv_signed k1) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x85cac-0x85cb8: the handler goes back to 0x85bf4 *)
      step. step.
      step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit (T1 + 6181604)) by lia.
      rewrite (lts_lit ((T1 + 6181604) mod 8 + 3) k1 ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply (J1 (T1 + 6181600) (T1 + 6181604)); lia. }
  (* ---- 0x85bc8: a7 = (GOT.n = OW.n) && (g_s.state = M.state), OW.n > 0 ---- *)
  assert (J0 : forall (s0b : bool) (x10 x11 : word),
    0 < TW.OW_n Bw -> s0b = ((TW.GOT_n Bw =? TW.OW_n Bw) && (TW.S_state Bw =? TW.M_state Bw)) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                x10 x11 a2 (Z_to_bv 64 6181600) (Z_to_bv 64 6238304) (Z_to_bv 64 2147450880)
                (Z_to_bv 64 (TW.OW_n Bw)) (Z_to_bv 64 (Z.b2z s0b))
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x85bc8) fc None mF (seg_rom rsegs))).
  { intros s0b x10 x11 HP Hs0.
    (* 0x85bc8-0x85bcc: a0 = 16; bltu a6,a0 *)
    step. step. rewrite css_ltu_lit by lia.
    destruct (Z.ltb_spec (TW.OW_n Bw) 16) as [L16|L16]; cbn [negb]; cbv iota.
    - (* OW.n < 16: cnt = OW.n; 0x85bd4-0x85bd8 t1 = 0, t0 = 1 *)
      step. step.
      apply (LOOP (Z.to_nat (TW.OW_n Bw)) 0 (TW.OW_n Bw) 0 (TW.OW_n Bw) s0b true);
        [lia | lia | lia | lia | lia | subst s0b; exact LP].
    - (* OW.n >= 16: 0x85bd0 a6 = 16; cnt = 16 *)
      step. step. step.
      apply (LOOP 16%nat 0 16 0 16 s0b true);
        [lia | lia | lia | lia | lia | subst s0b; exact LP]. }
  (* ---- 0x85b3c-0x85b48: a3 = GOT, a4 = OW ---- *)
  step. step. step. step.
  (* ---- 0x85b4c-0x85b84: the five pairs ---- *)
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 196 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 196) with TW.A_GOT_e2 in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_e2) with (TW.GOT_e2 Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 196 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 196) with TW.A_OW_e2 in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_e2) with (TW.OW_e2 Bw). clear RDo.
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite C1. cbn [negb]. cbv iota.
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 200 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 200) with TW.A_GOT_e3 in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_e3) with (TW.GOT_e3 Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 200 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 200) with TW.A_OW_e3 in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_e3) with (TW.OW_e3 Bw). clear RDo.
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite C2. cbn [negb]. cbv iota.
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 220 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 220) with TW.A_GOT_ndata in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_ndata) with (TW.GOT_ndata Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 220 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 220) with TW.A_OW_ndata in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_ndata) with (TW.OW_ndata Bw). clear RDo.
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite C3. cbn [negb]. cbv iota.
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 208 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 208) with TW.A_GOT_desk in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_desk) with (TW.GOT_desk Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 208 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 208) with TW.A_OW_desk in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_desk) with (TW.OW_desk Bw). clear RDo.
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite C4. cbn [negb]. cbv iota.
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 212 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 212) with TW.A_GOT_foreign in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_foreign) with (TW.GOT_foreign Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 212 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 212) with TW.A_OW_foreign in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_foreign) with (TW.OW_foreign Bw). clear RDo.
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite C5. cbn [negb]. cbv iota.
  (* ---- 0x85b88-0x85b98: a0 = CELL_K; a1 = GOT.n; a6 = OW.n; a5 = 0x7fff8000 ---- *)
  assert (RDG : ov_read_bytes rsegs mF (wa 671888) 8 = Some (le8 (wa 707064))).
  { replace (wa 671888) with (wa (671888 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 671888 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  assert (RDC : ov_read_bytes rsegs mF (wa 707064) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 707064) with (wa (707064 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 707064 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  step. step. clear RDG.
  pose proof (css_rd mF Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 0 4 HWF TMAP_A_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)) as RDg.
  unfold TA_GOT in RDg. change (TW.OFF_GOT + 0) with TW.A_GOT_n in RDg.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_GOT_n) with (TW.GOT_n Bw). clear RDg.
  pose proof (css_rd mF Bw TW.OFF_OW TA_OW TW.SZ_OW 0 4 HWF TMAP_A_OW ltac:(lia)
    ltac:(unfold TW.SZ_OW; lia)) as RDo.
  unfold TA_OW in RDo. change (TW.OFF_OW + 0) with TW.A_OW_n in RDo.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_OW_n) with (TW.OW_n Bw). clear RDo.
  step. clear RDC.
  (* ---- 0x85b9c bne a1,a6 to 0x85bc0 ---- *)
  step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range).
  (* the destruct also turns the test in J0 and LP into its value *)
  destruct (Z.eqb_spec (TW.GOT_n Bw) (TW.OW_n Bw)) as [En|En]; cbn [negb]; cbv iota.
  - (* GOT.n = OW.n: 0x85ba0-0x85bac a0 = g_s.state, a1 = M.state *)
    step. step.
    pose proof (css_rd mF Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 HWF TMAP_A_g_s ltac:(lia)
      ltac:(unfold TW.SZ_g_s; lia)) as RDs.
    unfold TA_g_s in RDs. change (TW.OFF_g_s + 112) with TW.A_S_state in RDs.
    step. rewrite lw_world. change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw). clear RDs.
    pose proof (css_rd mF Bw TW.OFF_M TA_M TW.SZ_M 12 4 HWF TMAP_A_M ltac:(lia)
      ltac:(unfold TW.SZ_M; lia)) as RDm.
    unfold TA_M in RDm. change (TW.OFF_M + 12) with TW.A_M_state in RDm.
    step. rewrite lw_world. change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw). clear RDm.
    (* 0x85bb0 bge zero,a6 to 0x85d24 *)
    step. rewrite css_lts0_s32 by lia.
    destruct (Z.ltb_spec 0 (TW.OW_n Bw)) as [NP|NP]; cbn [negb]; cbv iota.
    + (* OW.n > 0: 0x85bb4-0x85bbc a7 = (g_s.state = M.state); j 0x85bc8 *)
      step. step. rewrite css_seqz_xor by (apply TWorldLemmas.s32_range).
      step.
      apply (J0 (TW.S_state Bw =? TW.M_state Bw)); [lia | reflexivity].
    + (* OW.n <= 0: the loop does not run, so g_s.state = M.state; 0x85d24 beq a0,a1 to the return *)
      rewrite css_loop_stop in LP by lia.
      injection LP as Hs0. cbn [andb] in Hs0.
      step. rewrite css_eqb_s32 by (apply TWorldLemmas.s32_range). rewrite Hs0. cbv iota.
      apply EPI.
  - (* GOT.n <> OW.n: 0x85bc0 a7 = 0; 0x85bc4 bge zero,a6 to the trap path *)
    step.
    step. rewrite css_lts0_s32 by lia.
    destruct (Z.ltb_spec 0 (TW.OW_n Bw)) as [NP|NP]; cbn [negb]; cbv iota.
    + apply (J0 false); [lia | reflexivity].
    + exfalso. rewrite css_loop_stop in LP by lia.
      injection LP as Hs0. cbn [andb] in Hs0. discriminate Hs0.
Qed.

Print Assumptions check_state_settle_holds_F.
