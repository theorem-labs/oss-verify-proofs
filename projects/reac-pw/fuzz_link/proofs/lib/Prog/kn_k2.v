(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), part 2: the chunk loop. The body of one chunk
   (+0x1d4: the empty cursor, the raw path, or the message path through k_msgloop of kn_kmsg.v), the latch
   (+0xce0) and the loop as an induction over the chunks left. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  kn_k1 memcpy_c memcpy memset_c memset.
Local Open Scope Z_scope.

Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z H. unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_wrap 32 (z + 2 ^ 31)) with ((z + 2 ^ 31) mod 2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

(* a byte-wide identity in b, the goal `lhs = rhs`, checked over the 256 values *)
Ltac byte_fun_eq b BR :=
  lazymatch goal with |- ?l = ?r =>
    let f := lazymatch eval pattern b in l with ?f _ => f end in
    let g := lazymatch eval pattern b in r with ?g _ => g end in
    change (f b = g b); apply (by_enum256 f g); [vm_compute; reflexivity | exact BR]
  end.

(* the loop body at 0x14364 (+0x1d4) for chunk ci; w38 is the 0x38 spill slot before `sd s1, 0x38(sp)` *)
Definition k_body_k (c : kfix) (n ci : Z) : Prop :=
  forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la j0 w38 mc kd atw wbj wnc,
  kspill c m j0 (Z_to_bv 64 n) w38 mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) wnc -> cells_size wnc = 16%nat ->
  kcore c m adv kbs j la -> 0 <= j <= ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (Z_to_bv 64 ci) x10 x11 x12
             x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 203648) (Z_to_bv 64 n) x23 (Z_to_bv 64 (kSP c + -120))
             x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14364) (kf_fc c) None m (seg_rom rsegs)).

(* the latch: the next chunk, or the epilogue and kernel's Post *)
Lemma k_latch : forall c, kf_ok c -> forall n ci, 1 <= n <= 3 -> 0 <= ci < n ->
  (ci + 1 < n -> k_body_k c n (ci + 1)) -> k_latch_k c n ci.
Proof.
  intros c HC n ci NR CIR BODY. unfold k_latch_k.
  intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y23 y25 y27 y28 y29 y30 y31 m adv kbs j la
    ((j0 & mc & kd & atw & SPL) & (wbj & WB) & (wnc & WNC & WNS) & KC & _ & _ & JR).
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. rewrite (swrap32_small (ci + 1)) by lia.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* the next chunk *)
    eapply BODY; [lia | exact SPL | exact WB | exact WNC | exact WNS | kcore_pack | lia].
  - (* the last chunk: the epilogue *)
    zstep.
    eapply k_exit; [ | | | exact ST | exact SPL | reflexivity | exact WB | exact WNC | exact WNS | exact FRS | ];
      [ lia | lia | lia | ].
    intros R' RP ST'.
    eapply (ko_fin c HC R' m kbs j adv la RP); [exact MU | exact WM | exact MI | exact ST' | exact NK | exact GI | lia
      | exact ADV | exact CUR | exact LA].
Qed.

(* the body of chunk ci *)
Lemma k_body : forall c, kf_ok c -> k_msgloop_stmt -> forall n ci, 1 <= n <= 3 -> 0 <= ci < n ->
  k_latch_k c n ci -> k_body_k c n ci.
Proof.
  intros c HC KMS n ci NR CIR LK. unfold k_body_k.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la j0 w38
    mc kd atw wbj wnc SPL WB WNC WNS KC JR.
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* the cursor is empty *)
    eapply k_c78; [exact HC | exact SPL | exact WB | exact WNC | exact WNS | kcore_pack | lia | lia | lia | exact LK].
  - zstep. zstep. zstep. zstep. zstep.
    match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
      pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv) (Z_to_bv 64 (kWP c + adv)) H ltac:(lia) ltac:(lia)
                    eq_refl) as RD end.
    replace (kWP c + adv - kWP c) with adv in RD by lia.
    zstep. pose proof (rdn1_range (kf_d c) adv ltac:(lia) ltac:(lia)) as BR. rewrite zx8_wz by lia. unfold wz.
    zstep. zstep. if_cases K2; zify_cond K2.
    + (* mode & 1: a raw chunk *)
      replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
      replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
      eapply k_raw with (adv := adv); [exact HC | exact SPL | exact WB | exact WNC | exact WNS | kcore_pack | lia | lia
        | lia | lia | exact LK].
    + zstep. zstep. zstep. zstep.
      memset_w c.
      zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
      * (* no message-count byte *)
        replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
        replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
        eapply k_c88 with (adv := adv + 1); [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia
          | exact LK].
      * zstep. zstep. zstep. zstep.
        match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
          pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv + 1) _ H ltac:(lia) ltac:(lia) eq_refl) as RD1 end.
        replace (kWP c + adv + 1 - kWP c) with (adv + 1) in RD1 by lia.
        zstep. pose proof (rdn1_range (kf_d c) (adv + 1) ltac:(lia) ltac:(lia)) as BR1. rewrite zx8_wz by lia. unfold wz.
        zstep. zstep. zstep. zstep. zstep. zstep.
        match goal with |- context [Z_to_bv 64 (rdn (kf_d c) (adv + 1) 1 + ?r)] =>
          replace (rdn (kf_d c) (adv + 1) 1 + r) with (rdn (kf_d c) (adv + 1) 1 mod 6)
            by (set (b := rdn (kf_d c) (adv + 1) 1) in *; clearbody b; byte_fun_eq b BR1) end.
        zstep. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
        -- (* m = 0 messages *)
           replace (kWP c + adv + 2) with (kWP c + (adv + 2)) in CUR by lia.
           replace (kWN c - adv + -2) with (kWN c - (adv + 2)) in CUR by lia.
           eapply k_c88 with (adv := adv + 2); [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia
             | lia | exact LK].
        -- zstep. zstep. zstep.
           replace (kWP c + adv + 2) with (kWP c + (adv + 2)) in CUR by lia.
           replace (kWN c - adv + -2) with (kWN c - (adv + 2)) in CUR by lia.
           pose proof (Z.mod_pos_bound (rdn (kf_d c) (adv + 1) 1) 6 ltac:(lia)) as MR.
           eapply (KMS c HC) with (adv := adv + 2) (mc := rdn (kf_d c) (adv + 1) 1 mod 6) (k := 0) (wn := 0).
           ++ eapply kmsg_intro; first [eassumption | lia | idtac].
           ++ lia.
           ++ intros. eapply k_c64; [exact HC | eassumption | exact LK].
Qed.

(* the loop: from the latch of any chunk ci < n *)
Lemma k_loop : forall c, kf_ok c -> k_msgloop_stmt -> forall n, 1 <= n <= 3 ->
  forall d ci, Z.to_nat (n - 1 - ci) = d -> 0 <= ci < n -> k_latch_k c n ci.
Proof.
  intros c HC KMS n NR d. induction d as [|d IH]; intros ci Ed CIR.
  - apply (k_latch c HC n ci NR CIR). intros H. lia.
  - apply (k_latch c HC n ci NR CIR). intros H.
    apply (k_body c HC KMS n (ci + 1) NR ltac:(lia)). apply IH; lia.
Qed.

(* the first chunk *)
Lemma k_first : forall c, kf_ok c -> k_msgloop_stmt -> forall n, 1 <= n <= 3 -> k_body_k c n 0.
Proof.
  intros c HC KMS n NR. apply (k_body c HC KMS n 0 NR ltac:(lia)).
  apply (k_loop c HC KMS n NR (Z.to_nat (n - 1 - 0)) 0 eq_refl ltac:(lia)).
Qed.
