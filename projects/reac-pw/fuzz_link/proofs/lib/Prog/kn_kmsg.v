(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), the message loop of one chunk, from its head
   0x143e4 (+0x254) to 0x14df4 (+0xc64): `k_msgloop : k_msgloop_stmt` (kn_k0.v).

   The loop body: the head reads the kind byte (or finds the input empty: kind 0), jumps through the table at
   .rodata 0x106c4 on kind % 8, and builds one message; every kind ends at the latch 0x14de0 (+0xc50) in the
   shape `k_after_msg` names. The kinds are lemmas of their own files: 1 and 2 (kn_kmsg_k12.v, through the
   nl_error contract), 3 and 5 (kn_kmsg_k35.v), 4 and 6 (kn_kmsg_k46.v), 0 and 7 (kn_k07.v `k_kind07`, through
   the attr_text contract). The latch counts k up: k + 1 < mc and !w.full goes back to the head, else the loop
   ends. The loop is proved by induction on mc - k (`k_loop`).
   The callee contracts nl_error and attr_text are Section hypotheses (the unit's form for leaf callees whose
   walks are other lanes'): after the Section, `k_msgloop : nl_error_contract -> attr_text_contract ->
   k_msgloop_stmt`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  nl_error_c attr_text_c kn_k07 kn_kmsg_lem kn_kmsg_k12 kn_kmsg_k35 kn_kmsg_k46.
Local Open Scope Z_scope.

(* the loop's end, the continuation k_msgloop_stmt gives, for a cursor at A or beyond *)
Definition kcont (c : kfix) (A : Z) (kbs : list byte) (j n ci mc : Z) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y27 y28 y29 y30 y31 : word)
         (m' : word -> option byte) (adv' : Z) (la' : list byte) (wn' wf' : Z),
    kmsg_st c m' adv' kbs j la' n ci mc wn' wf' -> A <= adv' ->
    evt rsegs (kf_Q c)
      (MS (mkR y1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) y5 y6 y7 (kf_a0 c) y9 y10 y11 y12 y13 y14 y15
               y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 (kSP c + -120)) y25 (Z_to_bv 64 (-4093)) y27 y28 y29 y30 y31)
          (kf_F c) (Z_to_bv 64 0x14df4) (kf_fc c) None m' (seg_rom rsegs)).

(* the loop's head at message k, for a cursor at A or beyond *)
Definition khead (c : kfix) (k A : Z) (kbs : list byte) (j n ci mc : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (adv : Z) (la : list byte) (wn : Z),
    kmsg_st c m adv kbs j la n ci mc wn 0 -> A <= adv ->
    KG c 0x143e4 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).

Lemma kcont_mono : forall c A A' kbs j n ci mc, kcont c A kbs j n ci mc -> A <= A' -> kcont c A' kbs j n ci mc.
Proof. unfold kcont. intros c A A' kbs j n ci mc H L. intros. eapply H; [eassumption |]. lia. Qed.

Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z H. unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_wrap 32 (z + 2 ^ 31)) with ((z + 2 ^ 31) mod 2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

(* ==========================================================================
   The latch, 0x14de0 (+0xc50) .. 0x14df0 (+0xc60)
   ========================================================================== *)

Lemma k_latch : forall c, kf_ok c -> forall k A kbs j n ci mc,
  0 <= k < mc -> kcont c A kbs j n ci mc ->
  (k + 1 < mc -> khead c (k + 1) A kbs j n ci mc) ->
  k_after_msg c k A kbs j n ci mc.
Proof.
  intros c HC k A kbs j n ci mc Hk HCO HH.
  unfold k_after_msg.
  intros y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y25 y27 y28 y29 y30 y31 m' adv' la' wn' wf'
    ST LA'.
  kctx c HC. pose proof ST as ST0. kmsg_unpack ST.
  zstep. zstep. zstep.
  rewrite swrap32_small by lia.
  if_cases HB; zify_cond HB.
  - (* k + 1 >= mc: the loop ends *)
    fold_mkR. eapply HCO; [exact ST0 | lia].
  - (* k + 1 < mc: w.full decides *)
    zstep.
    change (sx32 (Z_to_bv 64 wf')) with (sx32 (wz wf')). rewrite (sx32_wz wf') by lia. unfold wz.
    zstep.
    if_cases HF; zify_cond HF.
    + (* !full: the head at k + 1 *)
      fold_mkR. assert (E : wf' = 0) by lia. subst wf'.
      eapply (HH ltac:(lia)); [exact ST0 | lia].
    + fold_mkR. eapply HCO; [exact ST0 | lia].
Qed.

(* ==========================================================================
   The head, 0x143e4 (+0x254) .. the jump at 0x14420 (+0x290)
   ========================================================================== *)

Lemma land7 : forall b, Z.land b 7 = b mod 8.
Proof. intros b. exact (Z.land_ones b 3 ltac:(lia)). Qed.

Section Loop.
Hypothesis NLE : nl_error_contract.
Hypothesis ATC : attr_text_contract.
(* the kind lemmas with the registers the head computes given as equations *)
Lemma k07w : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn kd : Z),
  kmsg_st c m adv kbs j la n ci mc wn 0 -> 0 <= k < mc -> (kd = 0 \/ kd = 7) -> k_after_msg c k adv kbs j n ci mc ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x14 = Z_to_bv 64 kd ->
  KG c 0x1443c m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la
    n ci mc k wn kd ST Hk Hkd HK E9 E14. subst x9 x14.
  exact (k_kind07 ATC c HC x1 x5 x6 x7 x10 x10 x11 x12 x13 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31
           m adv kbs j la n ci mc k wn kd ST Hk Hkd HK).
Qed.

Lemma k2w : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m A kbs j la n ci mc wn 0 -> 1 <= A -> 0 <= k < mc -> k_after_msg c k A kbs j n ci mc ->
  x9 = Z_to_bv 64 (kWN c - A) -> x10 = Z_to_bv 64 (kWN c - A + 1) -> x11 = Z_to_bv 64 (kWP c + A - 1) ->
  KG c 0x14a10 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la
    n ci mc k wn ST HA Hk HK E9 E10 E11. subst x9 x10 x11.
  exact (k2 NLE c HC x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31
           m A kbs j la n ci mc k wn ST HA Hk HK).
Qed.

Lemma k_head : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m adv kbs j la n ci mc wn 0 -> 0 <= k < mc -> k_after_msg c k adv kbs j n ci mc ->
  KG c 0x143e4 m (KR c k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la
    n ci mc k wn ST Hk HK.
  kctx c HC. pose proof ST as ST0. kmsg_unpack ST. kgl GI.
  zstep. zstep.
  if_cases HB; zify_cond HB.
  - (* the input is empty: kind 0 with no byte *)
    zstep. zstep. fold_mkR.
    eapply (k07w c HC); [exact ST0 | exact Hk | left; reflexivity | exact HK | f_equal; lia | reflexivity].
  - (* the kind byte *)
    do 5 zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv) (wa (kWP c + adv)) IN ltac:(lia) ltac:(lia)
                    eq_refl) as HR end.
    zstep.
    replace (kWP c + adv - kWP c) with adv by lia.
    rewrite zx8_wz by (apply rdn1_range; lia).
    pose proof (rdn1_range (kf_d c) adv ltac:(lia) ltac:(lia)) as Hb.
    set (b := rdn (kf_d c) adv 1) in *. clearbody b.
    replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
    replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ST1 : kmsg_st c mm (adv + 1) kbs j la n ci mc wn 0) by (kpack; lia) end.
    pose proof (k_after_msg_mono c k adv (adv + 1) kbs j n ci mc HK ltac:(lia)) as HK1.
    zstep. zstep.
    unfold wz. rewrite unsigned_lit by lia. rewrite land7.
    (* the jump table at .rodata 0x106c4, one case per kind % 8 *)
    assert (C : b mod 8 = 0 \/ b mod 8 = 1 \/ b mod 8 = 2 \/ b mod 8 = 3 \/ b mod 8 = 4 \/ b mod 8 = 5 \/
                b mod 8 = 6 \/ b mod 8 = 7) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; rewrite C; do 6 zstep; fold_mkR.
    + eapply (k07w c HC); [exact ST1 | exact Hk | left; reflexivity | exact HK1 | f_equal; lia | reflexivity].
    + eapply (k1 NLE c HC); [exact ST1 | exact Hk | exact HK1].
    + eapply (k2w c HC); [exact ST1 | lia | exact Hk | exact HK1 | f_equal; lia | f_equal; lia | f_equal; lia].
    + eapply (k3 c HC); [exact ST1 | exact Hk | exact HK1].
    + eapply (k4 c HC); [exact ST1 | exact Hk | exact HK1].
    + eapply (k5 c HC); [exact ST1 | exact Hk | exact HK1].
    + eapply (k6 c HC); [exact ST1 | exact Hk | exact HK1].
    + eapply (k07w c HC); [exact ST1 | exact Hk | right; reflexivity | exact HK1 | f_equal; lia | reflexivity].
Qed.

(* ==========================================================================
   The loop: induction on the messages left, mc - k
   ========================================================================== *)

Lemma k_loop : forall c, kf_ok c -> forall (d : nat) k A kbs j n ci mc,
  Z.of_nat d = mc - k -> 0 <= k < mc -> kcont c A kbs j n ci mc -> khead c k A kbs j n ci mc.
Proof.
  intros c HC d. induction d as [|d IH]; intros k A kbs j n ci mc Ed Hk HCO.
  - lia.
  - unfold khead.
    intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv la wn ST LA.
    pose proof (kcont_mono c A adv kbs j n ci mc HCO LA) as HCO'.
    eapply (k_head c HC); [exact ST | exact Hk |].
    apply (k_latch c HC k adv kbs j n ci mc Hk HCO').
    intros Hk1. apply (IH (k + 1) adv kbs j n ci mc); [lia | lia | exact HCO'].
Qed.

Lemma k_msgloop : k_msgloop_stmt.
Proof.
  unfold k_msgloop_stmt.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la
    n ci mc k wn ST Hk HCO.
  exact (k_loop c HC (Z.to_nat (mc - k)) k adv kbs j n ci mc ltac:(lia) Hk HCO
           x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv la wn ST
           (Z.le_refl adv)).
Qed.

End Loop.
