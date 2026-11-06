(* Proof of check_latest_drain_contract_F (check_latest_drain_F_c.v; image A, entry 0x85fdc, frame 16 bytes), with
   StepF's step: every access side goal is closed from the rng fact of the accessed range.

   The walk (listing DgnTransportList.v, the 77 slots of the function):
     0x85fdc-0x85fe0  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk. It is the only store.
     0x85fe4-0x85fec  a2 = M (0x5df160); a0 = the 4-byte load at 0x5df1a8 = M.display_sent, sign-extended.
     0x85ff0          beq a0,zero goes to 0x86014 (a3 = 0); else
     0x85ff4-0x86010    a1 = M.last_display, a0 = g_now, a3 = g_cfg.display_gap_us; a0 = a0 - a1;
                        a3 = (a0 <u a3); j 0x86018.
                      So at 0x86018 a3 = b2z (negb allow) of the model's allow (dr_allow).
     0x86018-0x8601c  a4 = the 4-byte load at 0x5df960 = g_nq, zero-extended.
     0x86020          beq a4,zero goes to 0x860c4 (a1 = 1 = b2z (negb false), the ready of the empty scan).
     0x86024-0x86048  a0 = [0xa4090] = 0xac9f8, a5 = g_q (0x5f1c00), a6 = [0xac9f8] = 0x7fff8000, a7 = 1,
                      t0 = 40, t1 = g_cmd (0x5e5400), a0 = a5.
     0x8604c-0x8609c  the scan, one iteration per drain_loop step with a0 = a5 = g_q + 4 i and a7 = i + 1:
       0x8604c-0x86058  the instrumented check of the 4-byte load at a = g_q + 4 i: a1 = the signed shadow byte
                        at (a >> 3) + 0x7fff8000; when it is not 0, 0x860a0-0x860ac test (a & 7) + 3 against it
                        and come back to 0x8605c;
       0x8605c-0x86068  a1 = g_q[i] = q, then a1 = g_cmd + 40 q + 8, the address of g_cmd[q].display;
       0x8606c-0x86078  the same instrumented check of that address, with the handler at 0x860b0-0x860b8;
       0x8607c-0x86084  a1 = g_cmd[q].display; a1 = (a1 <> 0); a1 = a1 & a3, that is b2z (negb ready'),
                        ready' = negb (truth display) || allow, the new ready of drain_loop;
       0x86088          bgeu a7,a4 (i + 1 >= g_nq) goes to 0x860c8;
       0x8608c-0x86094  a0, a5 += 4; a7 += 1;
       0x86098-0x8609c  beq a1,zero (ready') goes to 0x860c8, else back to 0x8604c.
     0x860c8-0x860f4  a0 = M.state; a0 <> 2 goes to the return; a0 = M.fly.on; a0 <> 0 goes to the return;
                      a0 = g_now, a2 = M.backoff_until; a0 = (a0 <u a2); a0 = (a0 | a1) & 1; beq a0,zero goes
                      to the trap 0x86104.
     0x860f8-0x86100  ld ra,8(sp); addi sp,sp,16; ret: the one return.

   How each check and branch is closed:
   - the two instrumented checks: the `addressable` premise of the loaded payload gives, for the checked address a,
     its shadow byte k with k = 0 or (a mod 8) + 3 < k <= 7 (shadow_of_load). When k = 0 the bne falls through to
     the load; else the handler compares (a & 7) + 3 with k and jumps back to the load. So neither
     __asan_report_load4 (0x8610c, 0x860c0) is reached. The two loaded addresses are inside the payloads because
     the model premise gives i < 1024 at g_q[i] and q < 1024 at g_cmd[q].display (dr_step).
   - every load reads the world: tw_bytes_at of TWorldG turns tw_at into the bytes_at fact the load step takes, and
     ld_world / lw_world / lwu_world name the loaded value as TWorld's accessor of Bw.
   - the trap path 0x86104 / 0x86108 (__asan_handle_no_return, abort) is not reached: the model premise gives
     (M_state = 2) && negb (truth M_fly_on) && (M_backoff_until <=? g_now) && ready = false, and on the path to
     0x860f4 the first two conjuncts hold, so (g_now <? M_backoff_until) || negb ready is true, which is a0 <> 0.
   - the world after: the run writes only its frame (munch), which the off_stk premise puts outside the hull
     [G_HARNESS_LO, G_HARNESS_HI) of the 18 payloads, so tw_at holds at the new memory with the same Bw
     (TMAP_A_kept), and the model gives Bw' = Bw.

   Templates: check_state_wake_F.v (image A's F leaf form) and the plain walk lib/Prog/T/check_latest_drain.v (the
   same model steps and the same loop invariant); the shadow-check shape is fuzz_decode's image-A
   check_cursor_step_F.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c check_latest_drain_c check_latest_drain_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.

(* ============================================================================
   The model: check_latest_drain_m's three facts
   ============================================================================ *)

(* the allow of fuzz_transport.c:787, as the model computes it *)
Definition dr_allow (B : list byte) : bool :=
  negb (TC.truth (TW.M_display_sent B))
  || (TW.Cfg_display_gap_us B <=? TS0.u64 (TW.g_now B - TW.M_last_display B)).

Lemma dr_model : forall B B', TC.check_latest_drain_m B = Some (B', tt) ->
  B' = B /\ exists rf, TC.drain_loop (S (Z.to_nat TC.CMDS_MAX)) B (dr_allow B) 0 false = Some rf /\
    ((TW.M_state B =? TC.S_ONLINE) && negb (TC.truth (TW.M_fly_on B))
     && (TW.M_backoff_until B <=? TW.g_now B) && rf) = false.
Proof.
  intros B B' H. unfold TC.check_latest_drain_m in H. cbv zeta in H.
  change (negb (TC.truth (TW.M_display_sent B))
          || (TW.Cfg_display_gap_us B <=? TS0.u64 (TW.g_now B - TW.M_last_display B))) with (dr_allow B) in H.
  destruct (TC.drain_loop (S (Z.to_nat TC.CMDS_MAX)) B (dr_allow B) 0 false) as [rf|] eqn:E; [|discriminate H].
  destruct ((TW.M_state B =? TC.S_ONLINE) && negb (TC.truth (TW.M_fly_on B))
            && (TW.M_backoff_until B <=? TW.g_now B) && rf) eqn:C; [discriminate H|].
  (* the world of the result, without injection on a world-carrying option *)
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H)
    as HB.
  cbv beta iota in HB.
  split; [symmetry; exact HB|]. exists rf. split; [reflexivity | exact C].
Qed.

(* one iteration of drain_loop, with the two bounds the instrumented loads need *)
Lemma dr_step : forall fuel B al i rf, TC.drain_loop (S fuel) B al i false = Some rf -> i < TW.g_nq B ->
  i < TC.CMDS_MAX /\ TW.Q_at B i < TC.CMDS_MAX /\
  TC.drain_loop fuel B al (i + 1) (negb (TC.truth (TW.Cmd_display B (TW.Q_at B i))) || al) = Some rf.
Proof.
  intros fuel B al i rf H Hi. cbn [TC.drain_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H. cbn [negb andb] in H.
  destruct (TC.CMDS_MAX <=? i) eqn:C1; [discriminate H|].
  destruct (TC.CMDS_MAX <=? TW.Q_at B i) eqn:C2; [discriminate H|].
  apply Z.leb_gt in C1, C2. split; [exact C1|]. split; [exact C2 | exact H].
Qed.

(* the exit of drain_loop: the result is the ready it was called with *)
Lemma dr_exit : forall fuel B al i r rf, TC.drain_loop fuel B al i r = Some rf ->
  (TW.g_nq B <= i \/ r = true) -> rf = r.
Proof.
  intros [|fuel] B al i r rf H D; [discriminate H|]. cbn [TC.drain_loop] in H.
  destruct D as [D | ->].
  - rewrite (proj2 (Z.ltb_ge _ _) D) in H. cbn [andb] in H. congruence.
  - cbn [negb] in H. rewrite andb_false_r in H. congruence.
Qed.

(* ============================================================================
   The world at the machine's view, and what survives the frame store
   ============================================================================ *)

(* a load of c bytes at b + k inside ONE payload, in the form the kit's load step reads *)
Lemma dr_rd : forall (m : word -> option byte) Bw o b n k (c : nat),
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
Lemma dr_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) -> tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *.
  exact (TMAP_A_kept m m' lo hi Bw H MU D).
Qed.

(* the frame store keeps `addressable`: a shadow byte of application memory is not in the frame, because both
   ends of the frame are application memory and shadow memory is not *)
Lemma dr_addr_tp : forall (m m' : word -> option byte) (sp p n : Z),
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

(* the shadow byte of g_q + o lies in the shadow range of g_q's payload (base 8-aligned, length a multiple of 8) *)
Lemma dr_shq : forall RNG o, rng RNG 2148230016 512 -> 0 <= o < 4096 ->
  rng RNG ((6233088 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148230016 512); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* the same for g_cmd's payload *)
Lemma dr_shc : forall RNG o, rng RNG 2148223616 5120 -> 0 <= o < 40960 ->
  rng RNG ((6181888 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148223616 5120); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* ============================================================================
   The machine words of the comparisons
   ============================================================================ *)

Lemma shr3 : forall z, Z.shiftr z 3 = z / 8.
Proof. intros z. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

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

(* `blt` / `bge` of a literal with a sign-extended shadow byte *)
Lemma lts_lit : forall (x : Z) (k : byte), -2^63 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* `sltu` of two words: the model's comparison, with the left side taken modulo 2^64 (the `sub` may be negative) *)
Lemma dr_sltu_mod : forall x y, 0 <= y < 2^64 ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (TC.b2z (TS0.u64 x <? y)).
Proof.
  intros x y Hy. unfold v_sltu, c_ltu, bv_ltu, TS0.u64, TC.b2z.
  rewrite unsigned_lit_wrap, (unsigned_lit y) by lia.
  destruct (x mod 2^64 <? y); reflexivity.
Qed.

Lemma dr_sltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (TC.b2z (x <? y)).
Proof.
  intros x y Hx Hy. rewrite (dr_sltu_mod x y Hy). unfold TS0.u64. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* `snez rd, rs` = `sltu rd, zero, rs`: the truth of a C scalar *)
Lemma dr_snez : forall d, -2^63 <= d < 2^63 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 d) = Z_to_bv 64 (TC.b2z (TC.truth d)).
Proof.
  intros d Hd. unfold v_sltu, c_ltu, bv_ltu, TC.truth, TC.b2z.
  rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.eqb_spec d 0) as [->|N]; cbn [negb].
  - rewrite Zmod_0_l. reflexivity.
  - replace (0 <? d mod 2^64) with true; [reflexivity|]. symmetry. apply Z.ltb_lt.
    assert (NZ : d mod 2^64 <> 0).
    { intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia. }
    pose proof (Z.mod_pos_bound d (2^64) ltac:(lia)). lia.
Qed.

Lemma dr_and_b2z : forall a b : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (TC.b2z a))) (bv_unsigned (Z_to_bv 64 (TC.b2z b))))
  = Z_to_bv 64 (TC.b2z (a && b)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma dr_or_b2z : forall a b : bool,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (TC.b2z a))) (bv_unsigned (Z_to_bv 64 (TC.b2z b))))
  = Z_to_bv 64 (TC.b2z (a || b)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma dr_andi1 : forall b : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (TC.b2z b))) 1) = Z_to_bv 64 (TC.b2z b).
Proof. intros [|]; reflexivity. Qed.

Lemma dr_b2z_eqb : forall b : bool, bv_eqb (Z_to_bv 64 (TC.b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

(* the `and` of the loop closes ready': negb (negb (truth display) || allow) *)
Lemma dr_demorgan : forall a b : bool, (a && negb b) = negb (negb a || b).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma bv_wrap64_1 : bv_wrap 64 1 = 1.
Proof. reflexivity. Qed.
Lemma bv_wrap64_7 : bv_wrap 64 7 = 7.
Proof. reflexivity. Qed.

(* ============================================================================
   The run
   ============================================================================ *)

Theorem check_latest_drain_holds_F : check_latest_drain_contract_F.
Proof.
  unfold check_latest_drain_contract_F, CHECK_LATEST_DRAIN, CHECK_LATEST_DRAIN_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' HW HM ST HLO HOFF CELLS AP1 AP2 OG OC ADQ ADC
    RFR RSENT RLAST RNOW RGAP RNQ RGOT RCELL RSHQ RQQ RSHC RCC RSTATE RFLY RBACK.
  (* the model: Bw' = Bw, the scan's result rf, and the trap condition that is false *)
  destruct (dr_model Bw Bw' HM) as [-> (rf & HL & HC)]. clear HM.
  (* the rng premises, with numeral bases (solve_acc1 takes its closed-literal branch only then) *)
  rewrite check_latest_drain_sent_at in RSENT. rewrite check_latest_drain_last_at in RLAST.
  rewrite check_latest_drain_gap_at in RGAP. rewrite check_latest_drain_state_at in RSTATE.
  rewrite check_latest_drain_fly_at in RFLY. rewrite check_latest_drain_backoff_at in RBACK.
  unfold TA_g_now in RNOW. unfold TA_g_nq in RNQ.
  unfold TA_g_q, TW.SZ_g_q in RQQ. unfold TA_g_cmd, TW.SZ_g_cmd in RCC.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL.
  change (shadow_addr TA_g_q) with 2148230016 in RSHQ. change (TW.SZ_g_q / 8) with 512 in RSHQ.
  change (shadow_addr TA_g_cmd) with 2148223616 in RSHC. change (TW.SZ_g_cmd / 8) with 5120 in RSHC.
  unfold TA_g_q, TW.SZ_g_q in ADQ. unfold TA_g_cmd, TW.SZ_g_cmd in ADC.
  (* the stack and the hull *)
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  unfold off_stk, GOT_CELL_K, CELL_K in OG, OC.
  (* the ranges of the world values the code loads *)
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_display_sent) as Rsent.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_state) as Rstate.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_fly_on) as Rfly.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_last_display 8) as Rlast.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_backoff_until 8) as Rback.
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8) as Rnow.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_Cfg_display_gap_us 4) as Rgap.
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_nq 4) as Rnq.
  change (8 * Z.of_nat 8) with 64 in Rlast, Rback, Rnow.
  change (8 * Z.of_nat 4) with 32 in Rgap, Rnq.
  change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw) in Rnow.
  change (TW.u_at Bw TW.OFF_g_nq 4) with (TW.g_nq Bw) in Rnq.
  change (TW.u_at Bw TW.A_M_last_display 8) with (TW.M_last_display Bw) in Rlast.
  change (TW.u_at Bw TW.A_M_backoff_until 8) with (TW.M_backoff_until Bw) in Rback.
  change (TW.u_at Bw TW.A_Cfg_display_gap_us 4) with (TW.Cfg_display_gap_us Bw) in Rgap.
  change (TW.s32_at Bw TW.A_M_display_sent) with (TW.M_display_sent Bw) in Rsent.
  change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw) in Rstate.
  change (TW.s32_at Bw TW.A_M_fly_on) with (TW.M_fly_on Bw) in Rfly.
  (* the frame *)
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  (* 0x85fdc-0x85fe0: the frame and the store of ra *)
  step. step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -16) ?cs |- _ =>
    set (FRC := cs) in H; rename H into FR end.
  (* the world, the two payload maps and the two runtime cells, after the only store *)
  assert (HWF : tw_at TMAP_A (csw_view mF) Bw).
  { apply (dr_kept m mF (bv_unsigned sp - 16) (bv_unsigned sp) Bw HW MU).
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia. }
  pose proof (dr_addr_tp m mF (bv_unsigned sp) 6233088 4096 ADQ MU AP1 AP2) as ADQF.
  pose proof (dr_addr_tp m mF (bv_unsigned sp) 6181888 40960 ADC MU AP1 AP2) as ADCF.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (CK0 : bytes_at rsegs mF 707064 (le8 (wa 2147450880)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact CK]).
  assert (GCK0 : bytes_at rsegs mF 671888 (le8 (wa 707064)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact GCK]).
  clear CK GCK CELLS.
  (* ---- the return, 0x860f8 ---- *)
  assert (EPI : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word),
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x860f8) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28.
    unfold FRC in FR.
    step.
    release_frame FR ST (bv_unsigned sp).
    step. step.
    apply evtF_done. unfold QQ. do 13 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact ST|]. split; [reflexivity | exact HWF]. }
  (* ---- after the scan, 0x860c8: a1 = b2z (negb rf) ---- *)
  assert (EXIT : forall (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 : word),
    x11 = Z_to_bv 64 (TC.b2z (negb rf)) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                x10 x11 (Z_to_bv 64 6156640) x13 x14 x15 x16 x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x860c8) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 ->.
    (* 0x860c8: a0 = M.state *)
    pose proof (dr_rd mF Bw TW.OFF_M TA_M TW.SZ_M 12 4 HWF TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia))
      as RDst.
    unfold TA_M in RDst. change (TW.OFF_M + 12) with TW.A_M_state in RDst.
    step. rewrite lw_world. change (TW.s32_at Bw TW.A_M_state) with (TW.M_state Bw). clear RDst.
    (* 0x860cc-0x860d0: a3 = 2; bne a0, a3 *)
    step. step.
    rewrite dr_eqb_lit by lia.
    destruct (Z.eqb_spec (TW.M_state Bw) 2) as [S2|S2]; cbn [negb]; cbv iota; [|apply EPI].
    (* 0x860d4: a0 = M.fly.on *)
    pose proof (dr_rd mF Bw TW.OFF_M TA_M TW.SZ_M 96 4 HWF TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia))
      as RDfl.
    unfold TA_M in RDfl. change (TW.OFF_M + 96) with TW.A_M_fly_on in RDfl.
    step. rewrite lw_world. change (TW.s32_at Bw TW.A_M_fly_on) with (TW.M_fly_on Bw). clear RDfl.
    (* 0x860d8: bne a0, zero *)
    step.
    rewrite dr_eqb0 by lia.
    destruct (Z.eqb_spec (TW.M_fly_on Bw) 0) as [F0|F0]; cbn [negb]; cbv iota; [|apply EPI].
    (* 0x860dc-0x860e0: a0 = g_now *)
    pose proof (dr_rd mF Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 HWF TMAP_A_g_now ltac:(lia)
      ltac:(unfold TW.SZ_g_now; lia)) as RDnw.
    unfold TA_g_now in RDnw. rewrite Z.add_0_r in RDnw.
    replace (TW.OFF_g_now + 0) with TW.OFF_g_now in RDnw by lia.
    step. step. rewrite ld_world. change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw). clear RDnw.
    (* 0x860e4: a2 = M.backoff_until *)
    pose proof (dr_rd mF Bw TW.OFF_M TA_M TW.SZ_M 56 8 HWF TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia))
      as RDbk.
    unfold TA_M in RDbk. change (TW.OFF_M + 56) with TW.A_M_backoff_until in RDbk.
    step. rewrite ld_world. change (TW.u_at Bw TW.A_M_backoff_until 8) with (TW.M_backoff_until Bw).
    clear RDbk.
    (* 0x860e8-0x860f0: a0 = (g_now <u backoff); a0 = a0 | a1; a0 = a0 & 1 *)
    step. rewrite dr_sltu_lit by lia.
    step. rewrite dr_or_b2z.
    step. rewrite ?bv_wrap64_1. rewrite dr_andi1.
    (* 0x860f4: beq a0, zero would reach the trap; the model rules it out *)
    step. rewrite dr_b2z_eqb.
    assert (CT : ((TW.g_now Bw <? TW.M_backoff_until Bw) || negb rf) = true).
    { apply Bool.not_false_is_true. intros E.
      apply Bool.orb_false_elim in E as [E1 E2].
      apply Z.ltb_ge in E1. apply Bool.negb_false_iff in E2.
      assert (HT : (TW.M_state Bw =? TC.S_ONLINE) && negb (TC.truth (TW.M_fly_on Bw))
                   && (TW.M_backoff_until Bw <=? TW.g_now Bw) && rf = true).
      { rewrite S2, F0, E2. rewrite (proj2 (Z.leb_le _ _) E1). reflexivity. }
      rewrite HT in HC. discriminate HC. }
    rewrite CT. cbn [negb]. cbv iota.
    apply EPI. }
  (* ---- the scan, 0x8604c ---- *)
  assert (LOOP : forall fuel i (x6 x7 x28 : word) (A0 A5 N : Z),
    TC.drain_loop fuel Bw (dr_allow Bw) i false = Some rf -> 0 <= i < TW.g_nq Bw ->
    A0 = 6233088 + 4 * i -> A5 = 6233088 + 4 * i -> N = i + 1 ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 6181888) x7 s0 s1
                (Z_to_bv 64 A0) x6 (Z_to_bv 64 6156640)
                (Z_to_bv 64 (TC.b2z (negb (dr_allow Bw)))) (Z_to_bv 64 (TW.g_nq Bw))
                (Z_to_bv 64 A5) (Z_to_bv 64 2147450880) (Z_to_bv 64 N)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x8604c) fc None mF (seg_rom rsegs))).
  { induction fuel as [|fuel IH]; intros i x6 x7 x28 A0 A5 N HLi Hi HA0 HA5 HN; [discriminate HLi|].
    destruct (dr_step fuel Bw (dr_allow Bw) i rf HLi ltac:(lia)) as (Hi1 & Hq & HL1).
    unfold TC.CMDS_MAX in Hi1, Hq.
    assert (RQ0 : 0 <= TW.Q_at Bw i) by (unfold TW.Q_at; apply TWorldLemmas.u_at_range).
    (* the state at 0x8607c, after both instrumented checks: a1 = the address of g_cmd[q].display *)
    assert (BODY2 : forall (y7 y28 : word),
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 6181888) y7 s0 s1
                  (Z_to_bv 64 A0) (Z_to_bv 64 (6181888 + TW.Q_at Bw i * 40 + 8)) (Z_to_bv 64 6156640)
                  (Z_to_bv 64 (TC.b2z (negb (dr_allow Bw)))) (Z_to_bv 64 (TW.g_nq Bw))
                  (Z_to_bv 64 A5) (Z_to_bv 64 2147450880) (Z_to_bv 64 N)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
            F (Z_to_bv 64 0x8607c) fc None mF (seg_rom rsegs))).
    { intros y7 y28.
      (* 0x8607c: a1 = g_cmd[q].display *)
      pose proof (dr_rd mF Bw TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * TW.Q_at Bw i + 8) 4 HWF TMAP_A_g_cmd
        ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)) as RDcd.
      unfold TA_g_cmd in RDcd.
      replace (6181888 + (40 * TW.Q_at Bw i + 8)) with (6181888 + TW.Q_at Bw i * 40 + 8) in RDcd by lia.
      replace (TW.OFF_g_cmd + (40 * TW.Q_at Bw i + 8)) with (TW.A_Cmd_display (TW.Q_at Bw i)) in RDcd
        by (unfold TW.A_Cmd_display; lia).
      step. rewrite lw_world.
      change (TW.s32_at Bw (TW.A_Cmd_display (TW.Q_at Bw i))) with (TW.Cmd_display Bw (TW.Q_at Bw i)).
      clear RDcd.
      pose proof (TWorldLemmas.s32_range Bw (TW.A_Cmd_display (TW.Q_at Bw i))) as Rcd.
      change (TW.s32_at Bw (TW.A_Cmd_display (TW.Q_at Bw i))) with (TW.Cmd_display Bw (TW.Q_at Bw i)) in Rcd.
      (* 0x86080-0x86084: a1 = (a1 <> 0); a1 = a1 & a3 = b2z (negb ready') *)
      step. rewrite dr_snez by lia.
      step. rewrite dr_and_b2z, dr_demorgan.
      remember (negb (TC.truth (TW.Cmd_display Bw (TW.Q_at Bw i))) || dr_allow Bw) as r1 eqn:ER1.
      (* 0x86088: bgeu a7, a4 *)
      step. rewrite dr_ltu_lit by lia.
      destruct (Z.ltb_spec N (TW.g_nq Bw)) as [Lt|Ge]; cbn [negb]; cbv iota.
      - (* the scan goes on *)
        step. step. step.
        (* 0x86098: beq a1, zero: ready' ends the scan *)
        step. rewrite dr_b2z_eqb.
        destruct r1.
        + assert (RFt : rf = true)
            by (apply (dr_exit fuel Bw (dr_allow Bw) (i + 1) true rf HL1); right; reflexivity).
          cbn [negb]. cbv iota. apply EXIT. rewrite RFt. reflexivity.
        + cbn [negb]. cbv iota.
          (* 0x8609c: back to 0x8604c *)
          step.
          apply (IH (i + 1)); [exact HL1 | lia | lia | lia | lia].
      - (* i + 1 >= g_nq: the scan ends with ready' *)
        assert (RFr : rf = r1)
          by (apply (dr_exit fuel Bw (dr_allow Bw) (i + 1) r1 rf HL1); left; lia).
        apply EXIT. rewrite RFr. reflexivity. }
    (* the state at 0x8605c, after the check of the load of g_q[i] *)
    assert (BODY : forall (y6 y7 y28 : word),
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 6181888) y7 s0 s1
                  (Z_to_bv 64 A0) y6 (Z_to_bv 64 6156640)
                  (Z_to_bv 64 (TC.b2z (negb (dr_allow Bw)))) (Z_to_bv 64 (TW.g_nq Bw))
                  (Z_to_bv 64 A5) (Z_to_bv 64 2147450880) (Z_to_bv 64 N)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
            F (Z_to_bv 64 0x8605c) fc None mF (seg_rom rsegs))).
    { intros y6 y7 y28.
      (* 0x8605c: a1 = g_q[i] = q *)
      pose proof (dr_rd mF Bw TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * i) 4 HWF TMAP_A_g_q ltac:(lia)
        ltac:(unfold TW.SZ_g_q; lia)) as RDq.
      unfold TA_g_q in RDq.
      replace (6233088 + 4 * i) with A5 in RDq by lia.
      step. rewrite lwu_world.
      change (TW.u_at Bw (TW.OFF_g_q + 4 * i) 4) with (TW.Q_at Bw i). clear RDq.
      (* 0x86060-0x86068: a1 = g_cmd + 40 q + 8 *)
      step. rewrite ?(unsigned_lit (TW.Q_at Bw i)) by lia.
      step. step.
      (* 0x8606c-0x86078: the check of the 4-byte load at that address *)
      destruct (shadow_of_load mF 6181888 40960 (TW.Q_at Bw i * 40 + 8) 4 ADCF ltac:(lia) ltac:(lia)
        ltac:(lia)) as (kc & MKc & SKc).
      replace (6181888 + (TW.Q_at Bw i * 40 + 8)) with (6181888 + TW.Q_at Bw i * 40 + 8) in MKc, SKc by lia.
      change (4 - 1) with 3 in SKc.
      pose proof (dr_shc RNG (TW.Q_at Bw i * 40 + 8) RSHC ltac:(lia)) as RKc.
      replace (6181888 + (TW.Q_at Bw i * 40 + 8)) with (6181888 + TW.Q_at Bw i * 40 + 8) in RKc by lia.
      unfold ASAN_K in MKc, RKc.
      pose proof (rd1 mF _ _ MKc) as RDkc.
      step. rewrite (unsigned_lit (6181888 + TW.Q_at Bw i * 40 + 8)) by lia. rewrite shr3.
      step. step.
      step. rewrite sxb_eq0.
      destruct SKc as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODY2.
      - rewrite (proj2 (Z.eqb_neq (bv_signed kc) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x860b0-0x860b8: the handler goes back to the load *)
        step. step.
        step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit (6181888 + TW.Q_at Bw i * 40 + 8)) by lia.
        rewrite (lts_lit ((6181888 + TW.Q_at Bw i * 40 + 8) mod 8 + 3) kc ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        apply BODY2. }
    (* 0x8604c-0x86058: the check of the 4-byte load at g_q + 4 i *)
    destruct (shadow_of_load mF 6233088 4096 (4 * i) 4 ADQF ltac:(lia) ltac:(lia) ltac:(lia))
      as (kq & MKq & SKq).
    replace (6233088 + 4 * i) with A0 in MKq, SKq by lia.
    change (4 - 1) with 3 in SKq.
    pose proof (dr_shq RNG (4 * i) RSHQ ltac:(lia)) as RKq.
    replace (6233088 + 4 * i) with A0 in RKq by lia.
    unfold ASAN_K in MKq, RKq.
    pose proof (rd1 mF _ _ MKq) as RDkq.
    step. rewrite (unsigned_lit A0) by lia. rewrite shr3.
    step.
    step.
    step. rewrite sxb_eq0.
    destruct SKq as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODY.
    - rewrite (proj2 (Z.eqb_neq (bv_signed kq) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x860a0-0x860ac: the handler goes back to the load *)
      step. step.
      step. rewrite ?bv_wrap64_7. rewrite land7, (unsigned_lit A0) by lia.
      rewrite (lts_lit (A0 mod 8 + 3) kq ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply BODY. }
  (* ---- 0x86018: a3 = b2z (negb allow) ---- *)
  assert (JOIN : forall (x10 x11 x13 : word), x13 = Z_to_bv 64 (TC.b2z (negb (dr_allow Bw))) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                x10 x11 (Z_to_bv 64 6156640) x13 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86018) fc None mF (seg_rom rsegs))).
  { intros x10 x11 x13 ->.
    (* 0x86018-0x8601c: a4 = g_nq *)
    pose proof (dr_rd mF Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4 HWF TMAP_A_g_nq ltac:(lia)
      ltac:(unfold TW.SZ_g_nq; lia)) as RDnq.
    unfold TA_g_nq in RDnq. rewrite Z.add_0_r in RDnq.
    replace (TW.OFF_g_nq + 0) with TW.OFF_g_nq in RDnq by lia.
    step. step. rewrite lwu_world. change (TW.u_at Bw TW.OFF_g_nq 4) with (TW.g_nq Bw). clear RDnq.
    (* 0x86020: beq a4, zero *)
    step. rewrite dr_eqb0 by lia.
    destruct (Z.eqb_spec (TW.g_nq Bw) 0) as [N0|N0]; cbv iota.
    - (* the queue is empty: ready is false *)
      step.
      assert (RF0 : rf = false)
        by (apply (dr_exit (S (Z.to_nat TC.CMDS_MAX)) Bw (dr_allow Bw) 0 false rf HL); left; lia).
      apply EXIT. rewrite RF0. reflexivity.
    - (* 0x86024-0x86048: the two runtime cells, the two payload bases, a7 = 1, t0 = 40 *)
      assert (RDG : ov_read_bytes rsegs mF (wa 671888) 8 = Some (le8 (wa 707064))).
      { replace (wa 671888) with (wa (671888 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs mF 671888 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia).
        reflexivity. }
      assert (RDC : ov_read_bytes rsegs mF (wa 707064) 8 = Some (le8 (wa 2147450880))).
      { replace (wa 707064) with (wa (707064 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs mF 707064 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia).
        reflexivity. }
      step. step. step. step. step. step. step. step. step. step.
      apply (LOOP (S (Z.to_nat TC.CMDS_MAX)) 0);
        [exact HL | lia | lia | lia | lia]. }
  (* ---- 0x85fe4-0x86014: allow ---- *)
  (* 0x85fe4-0x85fe8: a2 = M *)
  step. step.
  (* 0x85fec: a0 = M.display_sent *)
  pose proof (dr_rd mF Bw TW.OFF_M TA_M TW.SZ_M 72 4 HWF TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia))
    as RDsn.
  unfold TA_M in RDsn. change (TW.OFF_M + 72) with TW.A_M_display_sent in RDsn.
  step. rewrite lw_world. change (TW.s32_at Bw TW.A_M_display_sent) with (TW.M_display_sent Bw). clear RDsn.
  (* 0x85ff0: beq a0, zero *)
  step. rewrite dr_eqb0 by lia.
  destruct (Z.eqb_spec (TW.M_display_sent Bw) 0) as [D0|D0]; cbv iota.
  - (* display_sent = 0: allow is true, a3 = 0 *)
    step.
    apply JOIN.
    unfold dr_allow, TC.truth. rewrite D0. reflexivity.
  - (* 0x85ff4-0x86010: a3 = (u64 (g_now - last_display) <u display_gap_us) *)
    pose proof (dr_rd mF Bw TW.OFF_M TA_M TW.SZ_M 64 8 HWF TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia))
      as RDld.
    unfold TA_M in RDld. change (TW.OFF_M + 64) with TW.A_M_last_display in RDld.
    step. step. rewrite ld_world.
    change (TW.u_at Bw TW.A_M_last_display 8) with (TW.M_last_display Bw). clear RDld.
    pose proof (dr_rd mF Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 HWF TMAP_A_g_now ltac:(lia)
      ltac:(unfold TW.SZ_g_now; lia)) as RDnw.
    unfold TA_g_now in RDnw. rewrite Z.add_0_r in RDnw.
    replace (TW.OFF_g_now + 0) with TW.OFF_g_now in RDnw by lia.
    step. rewrite ld_world. change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw). clear RDnw.
    pose proof (dr_rd mF Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 48 4 HWF TMAP_A_g_cfg ltac:(lia)
      ltac:(unfold TW.SZ_g_cfg; lia)) as RDgp.
    unfold TA_g_cfg in RDgp. change (TW.OFF_g_cfg + 48) with TW.A_Cfg_display_gap_us in RDgp.
    step. step. rewrite lwu_world.
    change (TW.u_at Bw TW.A_Cfg_display_gap_us 4) with (TW.Cfg_display_gap_us Bw). clear RDgp.
    (* 0x86008-0x8600c: a0 = g_now - last_display; a3 = (a0 <u a3) *)
    step. rewrite (unsigned_lit (TW.g_now Bw)) by lia.
    rewrite (unsigned_lit (TW.M_last_display Bw)) by lia.
    step. rewrite dr_sltu_mod by lia.
    (* 0x86010: j 0x86018 *)
    step.
    apply JOIN.
    unfold dr_allow.
    replace (negb (TC.truth (TW.M_display_sent Bw))) with false
      by (unfold TC.truth; rewrite (proj2 (Z.eqb_neq _ _) D0); reflexivity).
    cbn [orb]. rewrite Z.ltb_antisym. reflexivity.
Qed.

Print Assumptions check_latest_drain_holds_F.
