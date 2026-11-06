From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0 nl_error_c kn_kmsg_lem.
Local Open Scope Z_scope.

(* reac-pw/fuzz_link, PLAIN build: kinds 1 and 2 of kernel's message loop (`k1_stmt`, `k2_stmt` of
   kn_kmsg_lem.v). Both kinds put an NLMSG_ERROR into w through nl_error and end at the latch 0x14de0.

   The cut:
   - `k_b18`, +0xb18 (0x14ca8): a0 = w, a2 any word nl_error's Pre accepts (at most 20, or at least 2^63);
     the call `jal nl_error` through the contract (`leaf_call`), then +0xb1c `j +0xc50` to the latch;
   - `k_ae0`, +0xae0 (0x14c70): a0 = a byte c; a1 = codes[c % 4] (read from .rodata 0x1070c, one case per
     c % 4), a2 = (slti(sext8 c < 0) - 1) | ((c << 57) >> 61), checked for all 256 bytes, then `k_b18`;
   - `k1`, +0x294 (0x14424): nl_error(w, 0, -1), into `k_b18`;
   - `k2`, +0x880 (0x14a10): no byte left gives c = 0 (+0xadc); else one more input byte c at kWP + A
     (the cursor moves to A + 1); both into `k_ae0`.
   The nl_error contract is the Section hypothesis NLE: after the Section, `k1 : nl_error_contract -> k1_stmt`
   and `k2 : nl_error_contract -> k2_stmt`. *)

(* nl_error's Post, read out of its contract *)
Definition ne_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(lazymatch eval cbv delta [nl_error_contract] in nl_error_contract with
        | leaf _ _ _ _ ?Q => exact Q end).

Lemma ne_post_ext : post_ext ne_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold ne_post in *. intros bs Hb.
  unfold arg in *. rewrite <- E1. apply H. rewrite E1. exact Hb.
Qed.

(* a cut of the 256 byte values checked one by one *)
Lemma cut_enum : forall (g : Z -> Z),
  forallb (fun z => (g z <=? 20) || (2 ^ 63 <=? g z)) (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> g z <= 20 \/ 2 ^ 63 <= g z.
Proof.
  intros g H z Hz. rewrite forallb_forall in H.
  assert (Hin : In z (map Z.of_nat (seq 0 256))).
  { replace z with (Z.of_nat (Z.to_nat z)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H z Hin). apply orb_true_iff in H.
  destruct H as [H|H]; [left | right]; apply Z.leb_le; exact H.
Qed.

Lemma land3 : forall b, Z.land b 3 = b mod 4.
Proof. intros b. exact (Z.land_ones b 2 ltac:(lia)). Qed.

Section K12.
Hypothesis NLE : nl_error_contract.

(* ==========================================================================
   +0xb18 (0x14ca8): nl_error(w, a1, a2), then j +0xc50
   ========================================================================== *)

Lemma k_b18 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 a2 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn wf : Z),
  kmsg_st c m A kbs j la n ci mc wn wf ->
  (bv_unsigned a2 <= 20 \/ 2 ^ 63 <= bv_unsigned a2) ->
  k_after_msg c k A kbs j n ci mc ->
  KG c 0x14ca8 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 (kSP c + -4216)) x11 a2 x13 x14 x15 x16 x17 x18 x21 x23
                     x25 x27 x28 x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 a2 m A kbs j la
    n ci mc k wn wf ST HA2 HK.
  kctx c HC. kmsg_unpack ST. kgl GI.
  assert (E1 : bv_unsigned (Z_to_bv 64 (kSP c + -4336)) = kSP c + -4336) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (kSP c + -4216)) = kSP c + -4216) by (apply unsigned_lit; lia).
  assert (WNC' : rw_cells rsegs m (kSP c + -4216 + 4096) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad])
    by (eapply rw_cells_at; [exact WNC | lia]).
  destruct (kw_nlw m (kSP c + -4216) wbj wn wf pad WB WNC' WNR WFR) as (bs & NA & NWF & _ & _).
  clear WNC'.
  zstep.
  fold_mkR.
  eapply (leaf_call _ _ _ _ _ NLE ne_post_ext (kf_Q c) (ko_qext c HC))
    with (F := kf_F c) (fc := kf_fc c) (m := m) (lo := kf_lo c).
  { cbv beta. exists bs. unfold apart_frame. rewrite mkR_a0, mkR_a2, mkR_sp. rewrite E1, E2.
    unfold NW_SIZE, NL_ERR_BODY. split; [exact NA|]. split; [exact NWF|]. split; [lia | exact HA2]. }
  { exact MI. }
  { rewrite E1. exact ST. }
  { rewrite E1. lia. }
  { rewrite E1. lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU1 WM1 MI1 ST1 PO.
  cbv beta in MU1, PO. rewrite ?mkR_a0 in MU1, PO. rewrite E1, E2 in MU1. rewrite E1 in ST1. rewrite E2 in PO.
  destruct (PO bs NA) as (bs' & NA' & NWF' & _). clear PO.
  assert (MUc : munch [(kSP c + -4416, kSP c + -4336); (kSP c + -4216, kSP c + -4216 + 4112)] m m').
  { unfold NW_SIZE in MU1. replace (kSP c + -4336 - 80) with (kSP c + -4416) in MU1 by lia. exact MU1. }
  clear MU1 WB WNC NA.
  transport_after_call rsegs m m' MUc WM1.
  clear MUc WM1. try clear MI.
  destruct (nlw_kw m' (kSP c + -4216) bs' NA' NWF') as (wbj' & pad' & WB' & WNC').
  replace (kSP c + -4216 + 4096) with (kSP c + -120) in WNC' by lia.
  unfold nlw_wf, NL_CHUNK_MAX in NWF'.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
  zstep.
  (* the register map is already `mkR` here: kto_latch without its fold_mkR *)
  unfold k_after_msg in HK. eapply HK; [kpack; lia | lia].
Qed.

(* ==========================================================================
   +0xae0 (0x14c70): a1 = codes[c % 4], a2 = the cut, a0 = w
   ========================================================================== *)

Lemma k_ae0 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (A : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn wf cv : Z),
  kmsg_st c m A kbs j la n ci mc wn wf -> 0 <= cv < 256 -> k_after_msg c k A kbs j n ci mc ->
  KG c 0x14c70 m (KR c k x1 x5 x6 x7 x9 (Z_to_bv 64 cv) x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28
                     x29 x30 x31).
Proof.
  intros c HC x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m A kbs j la
    n ci mc k wn wf cv ST Hcv HK.
  kctx c HC. pose proof ST as ST0. kmsg_unpack ST.
  do 8 zstep.
  (* the lw of codes[c % 4]: one literal address per case *)
  assert (Hr : Z.land cv 3 = 0 \/ Z.land cv 3 = 1 \/ Z.land cv 3 = 2 \/ Z.land cv 3 = 3)
    by (rewrite land3; lia).
  destruct Hr as [R|[R|[R|R]]]; rewrite R;
    do 6 zstep; fold_mkR;
    (eapply (k_b18 c HC); [exact ST0 | | exact HK]);
    (* the cut: (slti(sext8 c < 0) - 1) | ((c << 57) >> 61), for each of the 256 bytes *)
    match goal with |- bv_unsigned ?w <= _ \/ _ =>
      let g := eval pattern cv in w in
      lazymatch g with ?gf _ =>
        exact (cut_enum (fun z => bv_unsigned (gf z)) ltac:(vm_compute; reflexivity) cv Hcv) end end.
Qed.

(* ==========================================================================
   The kinds
   ========================================================================== *)

Lemma k1 : k1_stmt.
Proof.
  unfold k1_stmt. intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31
    m A kbs j la n ci mc k wn ST Hk HK.
  kctx c HC.
  do 4 zstep.
  fold_mkR.
  eapply (k_b18 c HC); [exact ST | | exact HK].
  right. apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma k2 : k2_stmt.
Proof.
  unfold k2_stmt. intros c HC x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31
    m A kbs j la n ci mc k wn ST HA Hk HK.
  kctx c HC. pose proof ST as ST0. kmsg_unpack ST. kgl GI.
  zstep.
  if_cases HB; zify_cond HB.
  - (* no byte left: c = 0 (+0xadc) *)
    zstep. fold_mkR.
    eapply (k_ae0 c HC) with (cv := 0); [exact ST0 | lia | exact HK].
  - (* the byte c at kWP + A; the cursor moves to A + 1 *)
    do 4 zstep.
    match goal with H : bytes_at rsegs ?mm (kWP c) (kf_d c) |- _ =>
      pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + A) (wa (kWP c + A)) H ltac:(lia) ltac:(lia) eq_refl)
        as RD end.
    replace (kWP c + A - kWP c) with A in RD by lia.
    zstep.
    rewrite zx8_wz by (apply rdn1_range; lia).
    zstep.
    (* the cursor's two words in the form kmsg_st names for A + 1 *)
    match goal with H : rw_cells rsegs ?mm (kCUR c) [C8 ?w1; C8 ?w2] |- _ =>
      replace w1 with (Z_to_bv 64 (kWP c + (A + 1))) in H by (f_equal; lia);
      replace w2 with (Z_to_bv 64 (kWN c - (A + 1))) in H by (f_equal; lia) end.
    assert (ADV' : 0 <= A + 1 <= kWN c) by lia. clear ADV.
    fold_mkR. unfold wz.
    eapply (k_ae0 c HC) with (A := A + 1) (cv := rdn (kf_d c) A 1);
      [kpack; lia | apply rdn1_range; lia | eapply k_after_msg_mono; [exact HK | lia]].
Qed.

End K12.
