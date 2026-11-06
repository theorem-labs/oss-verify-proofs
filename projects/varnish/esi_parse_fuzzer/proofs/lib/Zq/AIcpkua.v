(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.

Module AIcpilj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition kHighMemBeg_z : Z := 0x10007fff8000.
Definition kHighShadowEnd_z : Z := 0x10007fff8000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shadow_ok_sub : forall (m : word -> option byte) a n a' n',
  shadow_ok m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 1 <= n' -> shadow_ok m a' n'.
Proof.
  (intros m a n a' n'; (first [ intro dR_2; dex2 dR_2 as ng lastb; dand3 dR_2 as NG SH LB | intro dR_2; dand5 dR_2 as ng lastb NG SH LB | intros (ng & lastb & NG & SH & LB) ]); intros Ha H1 H2 H3).
  pose proof (bytes_at_bound _ _ _ _ SH) as B. rewrite length_app, zeros_length in B. cbn [length] in B.
  destruct (Z_lt_le_dec ((a' + n' - 1) / 8) ((a + n - 1) / 8)) as [LT | GE].
  - (* [comment removed for export] *)
    exists (Z.to_nat ((a' + n' - 1) / 8 - a' / 8)), 0. split; [mlia|]. split; [|left; reflexivity].
    replace (zeros (Z.to_nat ((a' + n' - 1) / 8 - a' / 8)) ++ [Z_to_bv 8 0])
      with (zeros (Z.to_nat ((a' + n' - 1) / 8 - a' / 8) + 1)) by (rewrite zeros_app; reflexivity).
    replace (a' / 8 + shadow_off) with (a / 8 + shadow_off + Z.of_nat (Z.to_nat (a' / 8 - a / 8))) by mlia.
    apply (shadow_zero_window m _ ng lastb _ _ SH). left. mlia.
  - (* [comment removed for export] *)
    assert (E : (a' + n' - 1) / 8 = (a + n - 1) / 8) by mlia.
    exists (Z.to_nat ((a' + n' - 1) / 8 - a' / 8)), lastb. split; [mlia|]. split.
    + (* [comment removed for export] *)
      apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
      * replace (a' / 8 + shadow_off) with (a / 8 + shadow_off + Z.of_nat (Z.to_nat (a' / 8 - a / 8))) by mlia.
        apply (shadow_zero_window m _ ng lastb _ _ SH). left. mlia.
      * rewrite zeros_length.
        replace (a' / 8 + shadow_off + Z.of_nat (Z.to_nat ((a' + n' - 1) / 8 - a' / 8)))
          with (a / 8 + shadow_off + Z.of_nat (length (zeros ng))) by (rewrite zeros_length; mlia).
        exact (bytes_at_app_r m _ _ _ SH).
    + destruct LB as [LB0 | LB1]; [left; exact LB0| right]. mlia.
Qed.

Lemma range_ok_sub : forall (m : word -> option byte) a n a' n',
  range_ok m a n -> a <= a' -> a' + n' <= a + n -> 1 <= n' -> range_ok m a' n'.
Proof.
  intros m a n a' n' RO H1 H2 H3. (first [ pose proof (RO) as dR_1; dand4 dR_1 as IR SOK Q1 Q2 | pose proof RO as (IR & SOK & Q1 & Q2) ]).
  assert (AF : 0 <= a /\ a + n + 8 <= 0x800000000000) by (unfold inmem_range in IR; lia).
  split; [unfold inmem_range in *; lia|].
  split; [eapply shadow_ok_sub; [exact SOK| lia| lia| lia| lia]|].
  split; apply (range_ok_mapped8_inner m a n); [exact RO| lia| exact RO| lia].
Qed.

(* [comment removed for export] *)
Definition zsh_bounds (SB : Z) (K : nat) (lo hi : Z) : Prop :=
  SB + 8 <= sha lo /\ sha hi + 8 <= SB + Z.of_nat K /\ SB + Z.of_nat K <= kHighShadowEnd_z
  /\ kHighMemBeg_z <= lo /\ hi + 16 <= 2^47 /\ lo <= hi.

Lemma zsh_bounds_sub : forall SB K lo hi lo' hi',
  zsh_bounds SB K lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' -> zsh_bounds SB K lo' hi'.
Proof.
  (intros SB K lo hi lo' hi'; (first [ intro dR_3; dand6 dR_3 as B1 B2 B3 B4 B5 B6 | intros (B1 & B2 & B3 & B4 & B5 & B6) ]); intros H1 H2 H3). unfold zsh_bounds, sha in *.
  assert (lo / 8 <= lo' / 8) by (apply Z.div_le_mono; lia). assert (hi' / 8 <= hi / 8) by (apply Z.div_le_mono; lia).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

Lemma zeros_sub : forall (m : word -> option byte) SB (K : nat) i (j : nat),
  bytes_at rsegs m SB (zeros K) -> 0 <= i -> i + Z.of_nat j <= Z.of_nat K -> bytes_at rsegs m (SB + i) (zeros j).
Proof.
  intros m SB K i j ZS Hi Hj.
  replace (zeros K) with (zeros (Z.to_nat i) ++ zeros (K - Z.to_nat i)) in ZS by (rewrite <- zeros_app; f_equal; lia).
  pose proof (bytes_at_app_r m _ _ _ ZS) as R. rewrite zeros_length, Z2Nat.id in R by lia.
  replace (zeros (K - Z.to_nat i)) with (zeros j ++ zeros (K - Z.to_nat i - j)) in R by (rewrite <- zeros_app; f_equal; lia).
  exact (bytes_at_app_l m _ _ _ R).
Qed.

Lemma zeros8_mapped8 : forall (m : word -> option byte) x, bytes_at rsegs m x (zeros 8) -> 0x60a000 <= x -> mapped8 m x.
Proof.
  intros m x B Hx. destruct (bytes8_word (zeros 8) eq_refl) as [w E]. rewrite E in B.
  eapply bytes_at_mapped8; [exact B| lia].
Qed.

Lemma range_ok_of_zeros : forall (m : word -> option byte) SB (K : nat) lo hi a n,
  bytes_at rsegs m SB (zeros K) -> zsh_bounds SB K lo hi ->
  lo <= a -> a + n <= hi -> 1 <= n -> range_ok m a n.
Proof.
  (intros m SB K lo hi a n ZS; (first [ intro dR_4; dand6 dR_4 as B1 B2 B3 B4 B5 B6 | intros (B1 & B2 & B3 & B4 & B5 & B6) ]); intros H1 H2 H3).
  unfold kHighShadowEnd_z, kHighMemBeg_z in *.
  assert (S1 : sha lo <= sha a) by (unfold sha; mlia).
  assert (S2 : sha (a + n - 1) <= sha hi) by (unfold sha; mlia).
  assert (S3 : sha a <= sha (a + n - 1)) by (unfold sha; mlia).
  split. { right. lia. }
  split.
  { exists (Z.to_nat ((a + n - 1) / 8 - a / 8)), 0. split; [mlia|]. split; [|left; reflexivity].
    replace (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8)) ++ [Z_to_bv 8 0])
      with (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8) + 1)) by (rewrite zeros_app; reflexivity).
    replace (a / 8 + shadow_off) with (SB + (sha a - SB)) by (unfold sha; lia).
    apply (zeros_sub m SB K); [exact ZS| lia| unfold sha in *; mlia]. }
  split.
  - replace (sha a - sha a mod 8) with (SB + (sha a - sha a mod 8 - SB)) by lia.
    apply zeros8_mapped8; [| unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m SB K); [exact ZS| mlia| mlia].
  - replace (sha (a + n - 1) - sha (a + n - 1) mod 8) with (SB + (sha (a + n - 1) - sha (a + n - 1) mod 8 - SB)) by lia.
    apply zeros8_mapped8; [| unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m SB K); [exact ZS| mlia| mlia].
Qed.
End AIcpilj.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Fixpoint wlow (W : list ivl) : Prop :=
  match W with [] => True
  | (lo, hi) :: W' => (kHighMemBeg_z <= lo \/ (0x60a000 <= lo /\ hi <= 2147446784) \/ hi <= 0x10000) /\ wlow W' end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_zone (a n : Z) : Prop :=
  (0x10000 <= a /\ a + n <= 0x60a000) \/ (2147446784 <= a /\ a + n <= kHighMemBeg_z).

Lemma wlow_outside : forall W x, wlow W -> in_zone x 1 -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x HW Hx; [exact I|]. destruct HW as [H1 H2]. cbn [outside].
  split; [unfold in_zone, kHighMemBeg_z in *; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Definition lowP (P : (word -> option byte) -> Prop) : Prop :=
  forall W m m', munch W m m' -> wlow W -> P m -> P m'.

Lemma low_disjoint : forall W a n, wlow W -> in_zone a n -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; [exact I|]. destruct HW as [H1 H2]. cbn [disjoint_from].
  split; [unfold in_zone, kHighMemBeg_z in *; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)

Lemma lowP_ro_cells : forall a cs, in_zone a (Z.of_nat (cells_size cs)) -> lowP (fun m => ro_cells rsegs m a cs).
Proof.
  intros a cs Ha W m m' MU HW B. eapply ro_cells_transport; [exact B| exact MU| apply low_disjoint; [exact HW| exact Ha]].
Qed.

Lemma lowP_mapped8 : forall a, in_zone a 8 -> lowP (fun m => mapped8 m a).
Proof.
  intros a Ha W m m' MU HW M i Hi.
  rewrite (MU (Z_to_bv 64 (a + i))). { exact (M i Hi). }
  rewrite unsigned_lit by (unfold in_zone, kHighMemBeg_z in Ha; lia). apply wlow_outside; [exact HW| unfold in_zone, kHighMemBeg_z in *; lia].
Qed.

Lemma lowP_and : forall P Q, lowP P -> lowP Q -> lowP (fun m => P m /\ Q m).
Proof. intros P Q HP HQ W m m' MU HW [H1 H2]. split; [eapply HP| eapply HQ]; eassumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma lowP_shadow_ok : forall a n, 0 <= a -> a + n + 8 <= 2^47 -> lowP (fun m => shadow_ok m a n).
Proof.
  (intros a n H0 Hn W m m' MU HW; (first [ intro dR_2; dex2 dR_2 as ng lastb; dand3 dR_2 as NG SH LB | intro dR_2; dand5 dR_2 as ng lastb NG SH LB | intros (ng & lastb & NG & SH & LB) ])). exists ng, lastb. split; [exact NG|]. split; [|exact LB].
  pose proof (bytes_at_bound _ _ _ _ SH) as BB.
  eapply bytes_at_transport; [exact SH| exact MU| apply low_disjoint; [exact HW|]].
  rewrite length_app, zeros_length in *. cbn [length] in *. unfold in_zone, shadow_off, kHighMemBeg_z in *. right.
  assert (A8 : 0 <= a / 8) by (apply Z.div_pos; lia). mlia.
Qed.

Lemma lowP_range_ok : forall a n, 0 <= n -> lowP (fun m => range_ok m a n).
Proof.
  (intros a n N0 W m m' MU HW; (first [ intro dR_3; dand4 dR_3 as IR SOK Q1 Q2 | intros (IR & SOK & Q1 & Q2) ])).
  assert (AF : 0 <= a /\ a + n + 8 <= 0x800000000000) by (unfold inmem_range in IR; lia).
  split; [exact IR|]. split; [exact (lowP_shadow_ok a n ltac:(lia) ltac:(lia) W m m' MU HW SOK)|].
  assert (A8 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (B8 : -1 <= (a + n - 1) / 8) by (change (-1) with ((-1) / 8); apply Z.div_le_mono; lia).
  assert (M1 : (a / 8 + 2147450880) mod 8 <= a / 8).
  { replace (a / 8 + 2147450880) with (a / 8 + 268431360 * 8) by lia. rewrite Z_mod_plus_full. apply Z.mod_le; lia. }
  pose proof (Z.mod_pos_bound ((a + n - 1) / 8 + 2147450880) 8 ltac:(lia)) as M2.
  pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)) as M0.
  assert (T1 : a / 8 <= (2^47) / 8) by (apply Z.div_le_mono; lia).
  assert (T2 : (a + n - 1) / 8 <= (2^47) / 8) by (apply Z.div_le_mono; lia).
  change ((2^47) / 8) with 17592186044416 in T1, T2.
  split.
  - refine (lowP_mapped8 _ _ W m m' MU HW Q1); unfold in_zone, sha, shadow_off, kHighMemBeg_z in *; right; mlia.
  - refine (lowP_mapped8 _ _ W m m' MU HW Q2); unfold in_zone, sha, shadow_off, kHighMemBeg_z in *; right; mlia.
Qed.

Lemma lowP_map_cells : lowP map_cells.
Proof.
  unfold map_cells. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia.
Qed.

(* [comment removed for export] *)
Ltac solve_wlow := cbn [wlow]; unfold kHighMemBeg_z in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.

(* [comment removed for export] *)
Ltac low_lemma_base P :=
  lazymatch P with
  | map_cells => constr:(lowP_map_cells)
  end.
Ltac low_lemma P := low_lemma_base P.

Ltac relow_all W m m' MU :=
  let HW := fresh "HW" in
  tryif assert (HW : wlow W) by solve_wlow then
    ((repeat match goal with
      | H : ?P m |- _ =>
          let lem := low_lemma P in
          let H2 := fresh "SF" in
          pose proof (lem W m m' MU HW H) as H2; clear H; rename H2 into H
      end); clear HW)
  else idtac "note: relow_all: footprint not provably low-free (wlow); low bundles not re-derived".

Ltac icpt_relow W m m' MU ::= relow_all W m m' MU.

Lemma munch_store1 : forall (m : word -> option byte) a bs n,
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  munch [(a, a + n)] m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs n Hn Ha Hl. apply munch_write; [apply munch_refl| exact Ha| lia|].
  cbn [inside]. left. lia.
Qed.

Ltac relow_store_hook m a bs n Hn Ha Hl :=
  let MUs := fresh "MUs" in
  tryif assert (MUs : munch [(a, (a + n)%Z)] m (write_to_mem m (wa a) bs)) by (exact (munch_store1 m a bs n Hn Ha Hl))
  then (relow_all constr:([(a, (a + n)%Z)]) m constr:(write_to_mem m (wa a) bs) MUs; clear MUs)
  else idtac "note: relow_store_hook: could not state the store's munch".
