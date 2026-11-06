(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma range_ok_repack : forall (m : word -> option byte) a n (ng : nat) (lastb : Z) (w1 w2 : word),
  inmem_range a n -> (1 <= n)%Z ->
  ((a + n - 1) / 8 - a / 8 = Z.of_nat ng)%Z ->
  bytes_at rsegs m (a / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) ->
  (lastb = 0 \/ ((a + n - 1) mod 8 < lastb <= 7))%Z ->
  bytes_at rsegs m (sha a - sha a mod 8) (le8 w1) ->
  bytes_at rsegs m (sha (a + n + -1) - sha (a + n + -1) mod 8) (le8 w2) ->
  range_ok m a n.
Proof.
  intros m a n ng lastb w1 w2 IR N1 NG SH LB Q1 Q2.
  assert (AF : (0 <= a /\ a + n + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  split; [exact IR|]. split; [exists ng, lastb; split; [exact NG| split; [exact SH| exact LB]]|].
  split; [eapply bytes_at_mapped8; [exact Q1| unfold sha, shadow_off; mlia]|].
  replace (a + n - 1)%Z with (a + n + -1)%Z by lia.
  eapply bytes_at_mapped8; [exact Q2| unfold sha, shadow_off; mlia].
Qed.

Lemma shadow_ok_prefix : forall (m : word -> option byte) a n k,
  shadow_ok m a n -> (0 <= a)%Z -> (1 <= k <= n)%Z -> shadow_ok m a k.
Proof.
  (intros m a n k; (first [ intro dR_3; dex2 dR_3 as ng lastb; dand3 dR_3 as NG SH LB | intro dR_3; dand5 dR_3 as ng lastb NG SH LB | intros (ng & lastb & NG & SH & LB) ]); intros Ha Hk).
  pose proof (bytes_at_bound _ _ _ _ SH) as B. rewrite length_app, zeros_length in B. cbn [length] in B.
  destruct (Z_lt_le_dec ((a + k - 1) / 8) ((a + n - 1) / 8)) as [LT | GE].
  - (* [comment removed for export] *)
    exists (Z.to_nat ((a + k - 1) / 8 - a / 8)), 0%Z. split; [mlia|]. split; [|left; reflexivity].
    replace (zeros (Z.to_nat ((a + k - 1) / 8 - a / 8)) ++ [Z_to_bv 8 0])
      with (zeros (Z.to_nat ((a + k - 1) / 8 - a / 8) + 1)) by (rewrite zeros_app; reflexivity).
    replace (a / 8 + shadow_off)%Z with (a / 8 + shadow_off + Z.of_nat 0)%Z by lia.
    apply (shadow_zero_window m _ ng lastb 0 _ SH). left. mlia.
  - (* [comment removed for export] *)
    assert (E : (a + k - 1) / 8 = (a + n - 1) / 8) by mlia.
    exists ng, lastb. split; [lia|]. split; [exact SH|].
    destruct LB as [LB0 | LB1]; [left; exact LB0| right]. mlia.
Qed.

(* [comment removed for export] *)
Lemma range_ok_mapped8_inner : forall (m : word -> option byte) a n x,
  range_ok m a n -> (a <= x <= a + n - 1)%Z -> mapped8 m (sha x - sha x mod 8).
Proof.
  (intros m a n x; (first [ intro dR_4; dand4 dR_4 as IR (ng & lastb & NG & SH & LB) Q1 Q2 | intros (IR & (ng & lastb & NG & SH & LB) & Q1 & Q2) ]); intros Hx i Hi).
  assert (AF : (0 <= a /\ a + n + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  pose proof (bytes_at_bound _ _ _ _ SH) as B. rewrite length_app, zeros_length in B. cbn [length] in B.
  set (w := (sha x - sha x mod 8 + i)%Z).
  destruct (Z_lt_le_dec w (sha a)) as [L1 | G1].
  - (* [comment removed for export] *)
    specialize (Q1 (w - (sha a - sha a mod 8))%Z ltac:(unfold w, sha in *; mlia)).
    replace (sha a - sha a mod 8 + (w - (sha a - sha a mod 8)))%Z with w in Q1 by lia. exact Q1.
  - destruct (Z_lt_le_dec (sha (a + n - 1)) w) as [L2 | G2].
    + (* [comment removed for export] *)
      specialize (Q2 (w - (sha (a + n - 1) - sha (a + n - 1) mod 8))%Z ltac:(unfold w, sha in *; mlia)).
      replace (sha (a + n - 1) - sha (a + n - 1) mod 8 + (w - (sha (a + n - 1) - sha (a + n - 1) mod 8)))%Z with w in Q2 by lia.
      exact Q2.
    + (* [comment removed for export] *)
      (first [ dand3 SH as _ _ RD | destruct SH as (_ & _ & RD) ]).
      specialize (RD (Z.to_nat (w - sha a)) ltac:(rewrite length_app, zeros_length; cbn [length]; unfold sha, shadow_off in *; mlia)).
      unfold mrd, wa in RD. rewrite Z2Nat.id in RD by (unfold sha in *; lia).
      replace (a / 8 + shadow_off + (w - sha a))%Z with w in RD by (unfold sha; lia).
      destruct (m (Z_to_bv 64 w)) eqn:Ew; [congruence|].
      rewrite icpt_seg_rom_none in RD.
      * destruct (nth_error (zeros ng ++ [Z_to_bv 8 lastb]) (Z.to_nat (w - sha a))) eqn:E2; [discriminate|].
        apply nth_error_None in E2. rewrite length_app, zeros_length in E2. cbn [length] in E2.
        unfold sha, shadow_off in *. mlia.
      * rewrite unsigned_lit by (unfold sha, shadow_off in *; mlia). unfold sha, shadow_off in *. mlia.
Qed.

Lemma range_ok_prefix : forall (m : word -> option byte) a n k,
  range_ok m a n -> (1 <= k <= n)%Z -> range_ok m a k.
Proof.
  intros m a n k RO Hk. (first [ pose proof (RO) as dR_2; dand4 dR_2 as IR SOK Q1 Q2 | pose proof RO as (IR & SOK & Q1 & Q2) ]).
  assert (AF : (0 <= a /\ a + n + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  split; [unfold inmem_range in *; lia|].
  split; [eapply shadow_ok_prefix; [exact SOK| lia| lia]|].
  split; [exact Q1|].
  apply (range_ok_mapped8_inner m a n); [exact RO| lia].
Qed.
