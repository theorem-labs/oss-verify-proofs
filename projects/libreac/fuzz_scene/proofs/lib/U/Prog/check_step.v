(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 779 of its 802 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import check_step_c bcmp_c memcpy_c reac_ctrl_parse_c reac_ctrl_checksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac slia ::= first [ exact I | lia | repeat split; try exact I; lia ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.


Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.

Lemma cells_bytes_map_C1 : forall l, cells_bytes (map C1 l) = l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma cells_wf_map_C1 : forall l, cells_wf (map C1 l).
Proof. induction l as [|x l IH]; cbn; [exact I|]. split; [exact I|exact IH]. Qed.

Lemma rw_cells_split2 : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma rw_cells_join2 : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma bytes_at_slice : forall m A l k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk.
  rewrite <- (CB3_bytes k n l Hk) in H.
  apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact H.
Qed.

Lemma ro_of_bytes : forall m A l, bytes_at rsegs m A l -> ro_cells rsegs m A (map C1 l).
Proof. intros m A l H. split; [apply cells_wf_map_C1 | rewrite cells_bytes_map_C1; exact H]. Qed.

Lemma wr_ro_disj : forall m A n B bs, mem_inv rsegs m -> wr_at rsegs m A n -> ro_bytes rsegs B bs ->
  0 < n -> (0 < length bs)%nat -> 0 <= B ->
  B + Z.of_nat (length bs) <= A \/ A + n <= B.
Proof.
  intros m A n B bs HI (HA & HAn & HW) HR Hn Hl HB.
  destruct (Z_le_gt_dec (B + Z.of_nat (length bs)) A) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (A + n) B) as [D2|D2]; [right; exact D2|]. exfalso.
  set (x := Z.max A B).
  destruct (nth_error bs (Z.to_nat (x - B))) as [bx|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  pose proof (ro_bytes_nth rsegs bs B _ bx HR E) as [_ RO].
  rewrite Z2Nat.id in RO by lia. replace (B + (x - B)) with x in RO by lia.
  pose proof (HW (x - A) ltac:(lia)) as W. replace (A + (x - A)) with x in W by lia.
  destruct (m (wa x)) as [bm|] eqn:Em.
  - pose proof (HI _ _ Em) as NR. congruence.
  - pose proof (wview_not_ro rsegs m (wa x) W Em) as NR. congruence.
Qed.

Lemma scene_fields_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_fields b k) = 31%nat.
Proof.
  intros b k Hb Hk. norm_nat_lits. unfold scene_fields, scene_payload, scene_off.
  destruct (Z.eqb_spec k 0); [subst; cbn [length app]; rewrite length_firstn, Hb; reflexivity|].
  destruct (Z.eqb_spec k 342).
  - cbn [length app]. rewrite length_app, length_firstn, length_skipn, Hb. reflexivity.
  - cbn [length app]. rewrite length_firstn, length_skipn, Hb. lia.
Qed.

Lemma scene_block_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. unfold scene_block. rewrite !length_app, scene_fields_length by assumption. reflexivity.
Qed.

Lemma cks_sum : forall S, 0 <= S -> (S + bv_unsigned (Z_to_bv 8 ((256 - S mod 256) mod 256))) mod 256 = 0.
Proof.
  intros S HS. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
  Z.div_mod_to_equations. lia.
Qed.

Lemma byte_sum_nonneg : forall l, 0 <= byte_sum l.
Proof.
  induction l as [|x l IH]; cbn [byte_sum fold_right]; [lia|].
  pose proof (bv_unsigned_in_range 8 x). unfold byte_sum in IH. lia.
Qed.

Lemma memcmp_model_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Ltac split_first H A B NewH :=
  lazymatch type of H with
  | rw_cells ?segs ?mm A (?c :: ?rest) =>
      let H2 := fresh "Hs" in
      destruct (rw_cells_split2 mm A B [c] rest H ltac:(cbn [cells_size csize Nat.add]; lia)) as [NewH H2];
      clear H; rename H2 into H
  end.

Lemma payload0' : forall b, scene_payload b 0 = [Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b.
Proof. reflexivity. Qed.

Lemma firstn_firstn' : forall (l : list byte) n, firstn n (firstn n l) = firstn n l.
Proof. intros l n. rewrite firstn_firstn, Nat.min_id. reflexivity. Qed.

Lemma app_split_len : forall (l1 l2 l3 l4 : list byte), length l1 = length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  induction l1 as [|x l1 IH]; intros l2 [|y l3] l4 HL HE; cbn in *; try discriminate; [split; [reflexivity|exact HE]|].
  injection HE as -> HE. destruct (IH l2 l3 l4 ltac:(lia) HE) as [-> ->]. split; reflexivity.
Qed.

Lemma segK : forall K, K <> 0 -> K <> 342 -> scene_seg K = 0.
Proof. intros K H0 H1. unfold scene_seg. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma lenK : forall K, K <> 0 -> K <> 342 -> scene_len K = 26.
Proof. intros K H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma payloadK : forall b K, K <> 0 -> K <> 342 ->
  scene_payload b K = firstn 26 (skipn (Z.to_nat (24 + 26 * (K - 1))) b).
Proof.
  intros b K H0 H1. unfold scene_payload, scene_off.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma lxor_small : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n); [|apply andb_false_r].
  subst n. rewrite Z.bits_above_log2; [reflexivity|lia|].
  destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Ltac zs := zstep; try (first [if_true | if_false]).

Lemma a4_eq : forall x, 0 <= x <= 2^64 - 34 ->
  Z.land ((Z.b2z (18446744073709551614 - x + 1 <? 1) + -1) mod 18446744073709551616) (18446744073709551614 - x)
  = 18446744073709551614 - x.
Proof.
  intros x Hx. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [Z.b2z].
  change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Ltac trap_t K := if_cases K; [zify_cond K; exfalso; lia | clear K].

Ltac uturn := zstep; zstep; let K := fresh "K" in trap_t K; zstep; zstep; zstep; zstep; zs.

Definition init_hd : list byte := map (Z_to_bv 8) [255; 255; 255; 255; 255; 255; 0; 64; 171; 0; 0; 1; 136; 25; 0; 0].
Definition scene_init : list byte := init_hd ++ repeat (Z_to_bv 8 0) 34.

Lemma swrap_k1 : forall k, 1 <= k <= 341 -> bv_swrap 32 (k + -1) = k + -1.
Proof.
  intros k Hk. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_k1 : forall k, 1 <= k <= 341 -> bv_signed (Z_to_bv 64 (k + -1)) = k + -1.
Proof.
  intros k Hk. rewrite zb_signed, unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt (k + -1) (2^63))) by lia. reflexivity.
Qed.

Ltac bad_pc t := lazymatch t with Z_to_bv 64 87892 => idtac | Z_to_bv 64 87896 => idtac end.

Ltac closed_t t := assert_fails (idtac; match t with context [?v] => is_var v end).

Ltac fold_land :=
  repeat match goal with |- context [Z.land ?x ?y] =>
    closed_t x; closed_t y;
    let v := eval vm_compute in (Z.land x y) in is_Zlit v; change (Z.land x y) with v
  end.

Ltac gfix :=
  fold_land;
  repeat match goal with
  | H : bv_swrap _ _ = _ |- _ => rewrite H
  | H : bv_signed _ = _ |- _ => rewrite H
  | H : Z.lxor _ _ = _ |- _ => rewrite H
  end;
  repeat match goal with
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
  | |- context [Z.lxor 18446744073709551615 ?x] => rewrite (Z.lxor_comm 18446744073709551615 x)
  end.

Ltac kfix K :=
  repeat match goal with
  | H : bv_swrap _ _ = _ |- _ => rewrite H in K
  | H : bv_signed _ = _ |- _ => rewrite H in K
  | H : Z.lxor _ _ = _ |- _ => rewrite H in K
  end;
  repeat match type of K with
  | context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia
  | context [Z.lxor 18446744073709551615 ?x] => rewrite (Z.lxor_comm 18446744073709551615 x) in K
  end;
  rewrite ?unsigned_lit_wrap in K.

Ltac res_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then ?T else ?E) _ _ _ _) =>
      gfix;
      tryif bad_pc T then
        first [ if_false
              | let K := fresh "K" in if_cases K; [zify_cond K; kfix K; exfalso; lia | clear K]
              | fail "res_if: taken branch is the stop" ]
      else tryif bad_pc E then
        first [ if_true
              | let K := fresh "K" in if_cases K; [clear K | zify_cond K; kfix K; exfalso; lia]
              | fail "res_if: fallthrough is the stop" ]
      else
        first [ if_true
              | if_false
              | let K := fresh "K" in if_cases K; [zify_cond K; kfix K; exfalso; lia | clear K]
              | let K := fresh "K" in if_cases K; [clear K | zify_cond K; kfix K; exfalso; lia]
              | fail "res_if: undetermined" ]
  | _ => idtac
  end.

Ltac zr_until a :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 a) _ _ _ _) => idtac
  | _ => zstep; res_if; zr_until a
  end.

Ltac bytes_by H :=
  lazymatch goal with |- bytes_at _ _ ?A _ =>
    lazymatch type of H with bytes_at _ _ ?A' _ =>
      replace A with A' by (first [reflexivity | rewrite unsigned_lit; lia | rewrite ?unsigned_lit_wrap; lia]); exact H
    end
  end.

Theorem check_step_holds :
  bcmp_contract -> memcpy_contract -> reac_ctrl_parse_contract -> reac_ctrl_checksum_verify_contract ->
  check_step_contract.
Proof.
  intros BCMP MEMC PARSE CKSV. unfold check_step_contract, CHECK_STEP, CHECK_STEP_K.
  unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE_K in PARSE.
  unfold reac_ctrl_checksum_verify_contract in CKSV.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo b HMI ST LO SP16 KR HBK HBB LB DBK DBB.
  norm_nat_lits.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  assert (Hbd : bv_unsigned a1 + 8904 <= 2^64)
    by (destruct (bytes_at_bound _ _ _ _ HBB) as [_ X]; rewrite LB in X; exact X).
  pose proof (scene_block_length b (bv_unsigned a2) LB ltac:(lia)) as LB34.
  assert (Hkd : bv_unsigned a0 + 34 <= 2^64)
    by (destruct (bytes_at_bound _ _ _ _ HBK) as [_ X]; rewrite LB34 in X; exact X).
  assert (LF : length (scene_fields b (bv_unsigned a2)) = 31%nat) by (apply scene_fields_length; [exact LB | lia]).
  set (B := scene_block b (bv_unsigned a2)) in *.
  assert (EB : scene_block b (bv_unsigned a2) = B) by reflexivity.
  clearbody B.
  destruct B as [|y0 B]; [discriminate LB34|].
  destruct B as [|y1 B]; [discriminate LB34|].
  destruct B as [|y2 B]; [discriminate LB34|].
  destruct B as [|y3 B]; [discriminate LB34|].
  destruct B as [|y4 B]; [discriminate LB34|].
  destruct B as [|y5 B]; [discriminate LB34|].
  destruct B as [|y6 B]; [discriminate LB34|].
  destruct B as [|y7 B]; [discriminate LB34|].
  destruct B as [|y8 B]; [discriminate LB34|].
  destruct B as [|y9 B]; [discriminate LB34|].
  destruct B as [|y10 B]; [discriminate LB34|].
  destruct B as [|y11 B]; [discriminate LB34|].
  destruct B as [|y12 B]; [discriminate LB34|].
  destruct B as [|y13 B]; [discriminate LB34|].
  destruct B as [|y14 B]; [discriminate LB34|].
  destruct B as [|y15 B]; [discriminate LB34|].
  destruct B as [|y16 B]; [discriminate LB34|].
  destruct B as [|y17 B]; [discriminate LB34|].
  destruct B as [|y18 B]; [discriminate LB34|].
  destruct B as [|y19 B]; [discriminate LB34|].
  destruct B as [|y20 B]; [discriminate LB34|].
  destruct B as [|y21 B]; [discriminate LB34|].
  destruct B as [|y22 B]; [discriminate LB34|].
  destruct B as [|y23 B]; [discriminate LB34|].
  destruct B as [|y24 B]; [discriminate LB34|].
  destruct B as [|y25 B]; [discriminate LB34|].
  destruct B as [|y26 B]; [discriminate LB34|].
  destruct B as [|y27 B]; [discriminate LB34|].
  destruct B as [|y28 B]; [discriminate LB34|].
  destruct B as [|y29 B]; [discriminate LB34|].
  destruct B as [|y30 B]; [discriminate LB34|].
  destruct B as [|y31 B]; [discriminate LB34|].
  destruct B as [|y32 B]; [discriminate LB34|].
  destruct B as [|y33 B]; [discriminate LB34|].
  destruct B; [|discriminate LB34]. clear LB34.
  assert (Y0 : y0 = Z_to_bv 8 0xcd) by exact (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y1 : y1 = Z_to_bv 8 0xea) by exact (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y2 : y2 = Z_to_bv 8 1) by exact (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y3 : y3 = Z_to_bv 8 (scene_seg (bv_unsigned a2))) by exact (f_equal (fun l => nth 3 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y4 : y4 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 4 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y5 : y5 = Z_to_bv 8 (scene_len (bv_unsigned a2))) by exact (f_equal (fun l => nth 5 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y6 : y6 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 6 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (SUM : (bv_unsigned y2 + bv_unsigned y3 + bv_unsigned y4 + bv_unsigned y5 + bv_unsigned y6 + bv_unsigned y7 + bv_unsigned y8 + bv_unsigned y9 + bv_unsigned y10 + bv_unsigned y11 + bv_unsigned y12 + bv_unsigned y13 + bv_unsigned y14 + bv_unsigned y15 + bv_unsigned y16 + bv_unsigned y17 + bv_unsigned y18 + bv_unsigned y19 + bv_unsigned y20 + bv_unsigned y21 + bv_unsigned y22 + bv_unsigned y23 + bv_unsigned y24 + bv_unsigned y25 + bv_unsigned y26 + bv_unsigned y27 + bv_unsigned y28 + bv_unsigned y29 + bv_unsigned y30 + bv_unsigned y31 + bv_unsigned y32 + bv_unsigned y33) mod 256 = 0).
  { assert (E : scene_fields b (bv_unsigned a2) ++
                [Z_to_bv 8 ((256 - byte_sum (scene_fields b (bv_unsigned a2)) mod 256) mod 256)]
                = [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 2) EB).
    apply app_inj_tail in E. destruct E as [EF EC].
    rewrite <- EC, EF.
    pose proof (cks_sum (byte_sum [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) (byte_sum_nonneg _)) as C.
    unfold byte_sum in C |- *. cbn [fold_right] in C |- *.
    match goal with |- ?X mod 256 = 0 => match type of C with ?Y mod 256 = 0 =>
      replace X with Y by lia; exact C end end. }
  pose proof (ro_of_bytes _ _ _ HBK) as HR. cbn [map] in HR.
  subst y0 y1 y2 y3 y4 y5 y6.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 128 junk [] [36; 2; 50; 40]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  split_first FR (bv_unsigned sp + -128) (bv_unsigned sp + -92) PP.
  split_first FR (bv_unsigned sp + -92) (bv_unsigned sp + -90) GG.
  split_first FR (bv_unsigned sp + -90) (bv_unsigned sp + -40) IFT.
  rename FR into SV.
  do 8 zstep.
  do 3 zstep; try if_false.
  do 2 zstep. trap_t T1.
  do 3 zstep; try if_false.
  do 2 zstep. trap_t T2.
  do 3 zstep; try if_false.
  do 2 zstep. trap_t T3.
  do 2 zstep; try if_false.
  do 9 zstep.
  rewrite (a4_eq (bv_unsigned a0)) by lia.
  do 32 uturn.
  zstep. zstep.
  pose proof (bv_unsigned_in_range 8 y7) as Ry7.
  pose proof (bv_unsigned_in_range 8 y8) as Ry8.
  pose proof (bv_unsigned_in_range 8 y9) as Ry9.
  pose proof (bv_unsigned_in_range 8 y10) as Ry10.
  pose proof (bv_unsigned_in_range 8 y11) as Ry11.
  pose proof (bv_unsigned_in_range 8 y12) as Ry12.
  pose proof (bv_unsigned_in_range 8 y13) as Ry13.
  pose proof (bv_unsigned_in_range 8 y14) as Ry14.
  pose proof (bv_unsigned_in_range 8 y15) as Ry15.
  pose proof (bv_unsigned_in_range 8 y16) as Ry16.
  pose proof (bv_unsigned_in_range 8 y17) as Ry17.
  pose proof (bv_unsigned_in_range 8 y18) as Ry18.
  pose proof (bv_unsigned_in_range 8 y19) as Ry19.
  pose proof (bv_unsigned_in_range 8 y20) as Ry20.
  pose proof (bv_unsigned_in_range 8 y21) as Ry21.
  pose proof (bv_unsigned_in_range 8 y22) as Ry22.
  pose proof (bv_unsigned_in_range 8 y23) as Ry23.
  pose proof (bv_unsigned_in_range 8 y24) as Ry24.
  pose proof (bv_unsigned_in_range 8 y25) as Ry25.
  pose proof (bv_unsigned_in_range 8 y26) as Ry26.
  pose proof (bv_unsigned_in_range 8 y27) as Ry27.
  pose proof (bv_unsigned_in_range 8 y28) as Ry28.
  pose proof (bv_unsigned_in_range 8 y29) as Ry29.
  pose proof (bv_unsigned_in_range 8 y30) as Ry30.
  pose proof (bv_unsigned_in_range 8 y31) as Ry31.
  pose proof (bv_unsigned_in_range 8 y32) as Ry32.
  pose proof (bv_unsigned_in_range 8 y33) as Ry33.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (scene_seg (bv_unsigned a2)))) as Rseg.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (scene_len (bv_unsigned a2)))) as Rlen.
  assert (U1 : bv_unsigned (Z_to_bv 8 1) = 1) by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
  unfold bv_modulus in *.
  pose proof ST as (L0 & _ & _).
  assert (UF90 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -90)) = bv_unsigned sp + -90) by (rewrite unsigned_lit; lia).
  assert (UF74 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -74)) = bv_unsigned sp + -74) by (rewrite unsigned_lit; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (U50 : bv_unsigned (Z_to_bv 64 50) = 50) by reflexivity.
  if_cases KS.
  - exfalso. zify_cond KS. apply KS.
    match type of KS with Z.land ?X 255 <> 0 => match type of SUM with ?Y mod 256 = 0 =>
      replace X with Y by (rewrite ?U1, ?U0 in *; lia) end end.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. exact SUM.
  - clear KS.
    zstep. if_cases K0; zify_cond K0.
    + destruct (Z.eq_dec (bv_unsigned a2) 342) as [K342|K342].
      * assert (EA : a2 = Z_to_bv 64 342) by (apply bv_eq; rewrite K342; reflexivity).
        subst a2. change (bv_unsigned (Z_to_bv 64 342)) with 342 in *.
        change (scene_seg 342) with 2 in *. change (scene_len 342) with 14 in *.
        zr_until 120996.
        fold_land.
        assert (E7 : (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer) ++
                     [Z_to_bv 8 ((256 - byte_sum (scene_fields b 342) mod 256) mod 256)]
                     = [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 7) EB).
        apply app_inj_tail in E7. destruct E7 as [E7 _].
        change [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] with ([y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20] ++ [y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) in E7.
        apply app_split_len in E7; [| rewrite length_firstn, length_skipn, LB; reflexivity].
        destruct E7 as [EPa EPt].
        pose proof (bytes_at_slice _ _ _ 7 14 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
        pose proof (bytes_at_slice _ _ _ (Z.to_nat 8890) 14 HBB ltac:(rewrite LB; apply Nat.leb_le; reflexivity)) as HRB.
        rewrite Z2Nat.id in HRB by lia.
        call BCMP.
        { bytes_by HL. }
        { bytes_by HRB. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 14))) with 14%nat. rewrite <- EPa.
          apply memcmp_model_refl. rewrite length_firstn, length_skipn, LB. apply Nat.leb_le. reflexivity. }
        { assumption. }
        zr_until 120996.
        pose proof (bytes_at_slice _ _ _ 21 12 HBK ltac:(cbn; lia)) as HL2. cbn [firstn skipn] in HL2.
        match goal with HMI' : mem_inv rsegs ?mm |- _ =>
          assert (HT : bytes_at rsegs mm 66454 scene_trailer)
            by (destruct (ro_cells_image rsegs mm 66454 scene_trailer HMI' ltac:(vm_compute; reflexivity)
                            ltac:(lia) ltac:(cbn; lia)) as [_ X];
                cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X)
        end.
        call BCMP.
        { bytes_by HL2. }
        { bytes_by HT. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 12))) with 12%nat. rewrite <- EPt.
          apply memcmp_model_refl. cbn. lia. }
        { assumption. }
        zr_until 121048.
        match goal with HMI' : mem_inv rsegs ?mm |- _ =>
          assert (HI : bytes_at rsegs mm 66466 scene_init)
            by (destruct (ro_cells_image rsegs mm 66466 scene_init HMI' ltac:(vm_compute; reflexivity)
                            ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia)) as [_ X];
                cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X);
          assert (DI : 66466 + 50 <= bv_unsigned sp + -90 \/ bv_unsigned sp + -90 + 50 <= 66466)
            by (destruct (wr_ro_disj mm (bv_unsigned sp + -90) 50 66466 scene_init HMI' (proj2 IFT)
                            (ro_bytes_b_sound rsegs scene_init 66466 ltac:(vm_compute; reflexivity))
                            ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia) ltac:(lia)) as [D|D];
                change (length scene_init) with 50%nat in D; lia)
        end.
        call MEMC.
        { bytes_by HI. }
        { reflexivity. }
        { rewrite UF90, U50. change (Z.to_nat 50) with 50%nat. exact IFT. }
        { rewrite ?unsigned_lit_wrap. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -90))) _ |- _ =>
            rewrite UF90, U50 in P; change (Z.to_nat 50) with 50%nat in P; rename P into IFT
        end.
        apply (rw_cells_split_CB rsegs _ _ [] 50 scene_init [] [16; 34]%nat) in IFT; [|reflexivity].
        cbn [app mk_CB_cells] in IFT.
        split_first IFT (bv_unsigned sp + -90) (bv_unsigned sp + -74) II.
        rename IFT into FTa.
        change (firstn 16 scene_init) with init_hd in II.
        zr_until 121048.
        call MEMC.
        { exact HBK. }
        { reflexivity. }
        { rewrite UF74, U34. change (Z.to_nat 34) with 34%nat. exact FTa. }
        { rewrite UF74, U34. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -74))) _ |- _ =>
            rewrite UF74, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
        end.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
        pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
        pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
        cbn [cells_bytes cbytes app firstn skipn] in BC.
        replace (bv_unsigned sp + -74 + Z.of_nat 2) with (bv_unsigned sp + -90 + 18) in BC by lia.
        clear IF.
        zr_until 88856.
        lazymatch type of ST with stk _ ?mm _ _ =>
          destruct (stk_split rsegs mm lo (bv_unsigned sp + -128 - 80) (bv_unsigned sp + -128) ST ltac:(lia)) as [STa STb]
        end.
        clear ST.
        match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { lia. }
        { lia. }
        { Z.div_mod_to_equations. lia. }
        { lia. }
        { exact STb. }
        { assumption. }
        { reflexivity. }
        { intros _. lia. }
        { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
          eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
        { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
        intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -128) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
        lazymatch type of MUc with munch _ ?mo ?mn =>
          transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
          try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
        end.
        destruct PO as [STp PO].
        specialize (PO ltac:(lia)).
        pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
        replace (ret_pc (Z_to_bv 64 87808)) with (Z_to_bv 64 87808) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -128) [CB 36 (snd (ctrlparse 50 ?FB))] =>
          assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
          apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 2);
                                        CB 2 [Z_to_bv 8 14; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                        CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
          [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
          rename PO into PP2
        end.
        zr_until 87988.
        match type of BC with bytes_at _ _ _ ?L =>
          eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -90) (bs := L);
                           [lia | lia | reflexivity | reflexivity | exact BC] | ]
        end.
        intros ms' PO. destruct PO as (a1' & a2' & a3' & a4' & a5' & EM). subst ms'.
        replace (ret_pc (Z_to_bv 64 87860)) with (Z_to_bv 64 87860) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match goal with |- context [blocksum ?L] =>
          assert (BSUM : blocksum L = 0)
            by (unfold blocksum; cbn [psum nth];
                match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                  replace X with Y by lia; exact SUM end end);
          rewrite BSUM
        end.
        cbn [Z.eqb].
        zstep. res_if.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -90) _ _ GG ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -92) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as FR.
        clear J1 J2 J3 SV FT2 II GG PP2.
        cbn [app] in FR.
        do 6 zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.
      * assert (SG : bv_signed a2 = bv_unsigned a2) by (rewrite zb_signed; destruct (Z.ltb_spec (bv_unsigned a2) (2^63)); lia).
        assert (LX : Z.lxor (bv_unsigned a2) 9223372036854775808 = bv_unsigned a2 + 9223372036854775808) by (apply lxor_small; lia).
        assert (SW1 : bv_swrap 32 (bv_unsigned a2 + -1) = bv_unsigned a2 + -1) by (apply swrap_k1; lia).
        assert (SA1 : bv_signed (Z_to_bv 64 (bv_unsigned a2 + -1)) = bv_unsigned a2 + -1) by (apply signed_k1; lia).
        assert (SEGK : scene_seg (bv_unsigned a2) = 0) by (apply segK; assumption).
        assert (LENK : scene_len (bv_unsigned a2) = 26) by (apply lenK; assumption).
        rewrite SEGK, LENK in *.
        zstep.
        rewrite LX.
        rewrite (proj2 (Z.ltb_lt (bv_unsigned a2 + 9223372036854775808) (342 + 9223372036854775808)) ltac:(lia)).
        cbn [Z.b2z].
        zr_until 120996.
        assert (E7 : scene_payload b (bv_unsigned a2) ++
                     [Z_to_bv 8 ((256 - byte_sum (scene_fields b (bv_unsigned a2)) mod 256) mod 256)]
                     = [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 7) EB).
        apply app_inj_tail in E7. destruct E7 as [E7 _].
        rewrite payloadK in E7 by assumption.
        pose proof (bytes_at_slice _ _ _ 7 26 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
        pose proof (bytes_at_slice _ _ _ (Z.to_nat (24 + 26 * (bv_unsigned a2 - 1))) 26 HBB ltac:(rewrite LB; lia)) as HRB.
        rewrite Z2Nat.id in HRB by lia.
        call BCMP.
        { bytes_by HL. }
        { bytes_by HRB. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 26))) with 26%nat. rewrite <- E7.
          apply memcmp_model_refl. rewrite length_firstn, length_skipn, LB. lia. }
        { assumption. }
        zr_until 121048.
        match goal with HMI' : mem_inv rsegs ?mm |- _ =>
          assert (HI : bytes_at rsegs mm 66466 scene_init)
            by (destruct (ro_cells_image rsegs mm 66466 scene_init HMI' ltac:(vm_compute; reflexivity)
                            ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia)) as [_ X];
                cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X);
          assert (DI : 66466 + 50 <= bv_unsigned sp + -90 \/ bv_unsigned sp + -90 + 50 <= 66466)
            by (destruct (wr_ro_disj mm (bv_unsigned sp + -90) 50 66466 scene_init HMI' (proj2 IFT)
                            (ro_bytes_b_sound rsegs scene_init 66466 ltac:(vm_compute; reflexivity))
                            ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia) ltac:(lia)) as [D|D];
                change (length scene_init) with 50%nat in D; lia)
        end.
        call MEMC.
        { bytes_by HI. }
        { reflexivity. }
        { rewrite UF90, U50. change (Z.to_nat 50) with 50%nat. exact IFT. }
        { rewrite ?unsigned_lit_wrap. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -90))) _ |- _ =>
            rewrite UF90, U50 in P; change (Z.to_nat 50) with 50%nat in P; rename P into IFT
        end.
        apply (rw_cells_split_CB rsegs _ _ [] 50 scene_init [] [16; 34]%nat) in IFT; [|reflexivity].
        cbn [app mk_CB_cells] in IFT.
        split_first IFT (bv_unsigned sp + -90) (bv_unsigned sp + -74) II.
        rename IFT into FTa.
        change (firstn 16 scene_init) with init_hd in II.
        zr_until 121048.
        call MEMC.
        { exact HBK. }
        { reflexivity. }
        { rewrite UF74, U34. change (Z.to_nat 34) with 34%nat. exact FTa. }
        { rewrite UF74, U34. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -74))) _ |- _ =>
            rewrite UF74, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
        end.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
        pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
        pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
        cbn [cells_bytes cbytes app firstn skipn] in BC.
        replace (bv_unsigned sp + -74 + Z.of_nat 2) with (bv_unsigned sp + -90 + 18) in BC by lia.
        clear IF.
        zr_until 88856.
        lazymatch type of ST with stk _ ?mm _ _ =>
          destruct (stk_split rsegs mm lo (bv_unsigned sp + -128 - 80) (bv_unsigned sp + -128) ST ltac:(lia)) as [STa STb]
        end.
        clear ST.
        match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { lia. }
        { lia. }
        { Z.div_mod_to_equations. lia. }
        { lia. }
        { exact STb. }
        { assumption. }
        { reflexivity. }
        { intros _. lia. }
        { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
          eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
        { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
        intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -128) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
        lazymatch type of MUc with munch _ ?mo ?mn =>
          transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
          try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
        end.
        destruct PO as [STp PO].
        specialize (PO ltac:(lia)).
        pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
        replace (ret_pc (Z_to_bv 64 87808)) with (Z_to_bv 64 87808) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -128) [CB 36 (snd (ctrlparse 50 ?FB))] =>
          assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
          apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                        CB 2 [Z_to_bv 8 26; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                        CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
          [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
          rename PO into PP2
        end.
        zr_until 87988.
        match type of BC with bytes_at _ _ _ ?L =>
          eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -90) (bs := L);
                           [lia | lia | reflexivity | reflexivity | exact BC] | ]
        end.
        intros ms' PO. destruct PO as (a1' & a2' & a3' & a4' & a5' & EM). subst ms'.
        replace (ret_pc (Z_to_bv 64 87860)) with (Z_to_bv 64 87860) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match goal with |- context [blocksum ?L] =>
          assert (BSUM : blocksum L = 0)
            by (unfold blocksum; cbn [psum nth];
                match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                  replace X with Y by lia; exact SUM end end);
          rewrite BSUM
        end.
        cbn [Z.eqb].
        zstep. res_if.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -90) _ _ GG ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -92) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as FR.
        clear J1 J2 J3 SV FT2 II GG PP2.
        cbn [app] in FR.
        do 6 zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.
    + assert (EA : a2 = Z_to_bv 64 0) by (apply bv_eq; rewrite K0; reflexivity).
      subst a2. change (bv_unsigned (Z_to_bv 64 0)) with 0 in *.
      change (scene_seg 0) with 1 in *. change (scene_len 0) with 24 in *.
      zr_until 120996.
      fold_land.
      assert (EP : firstn 24 (skipn 9 (scene_block b 0)) = firstn 24 b).
      { unfold scene_block, scene_fields. rewrite payload0'. cbn [skipn app]. rewrite ?skipn_O.
        rewrite firstn_app, length_firstn, LB. cbn [Nat.min Nat.sub firstn]. rewrite app_nil_r.
        apply firstn_firstn'. }
      rewrite EB in EP. cbn [firstn skipn] in EP.
      pose proof (bytes_at_slice _ _ _ 9 24 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
      pose proof (bytes_at_slice _ _ _ 0 24 HBB ltac:(rewrite LB; cbn; lia)) as HRB.
      change (skipn 0 b) with b in HRB. rewrite Z.add_0_r in HRB.
      call BCMP.
      { bytes_by HL. }
      { bytes_by HRB. }
      { change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat. rewrite EP.
        apply memcmp_model_refl. rewrite length_firstn, LB. cbn. lia. }
      { assumption. }
      zr_until 121048.
      match goal with HMI' : mem_inv rsegs ?mm |- _ =>
        assert (HI : bytes_at rsegs mm 66466 scene_init)
          by (destruct (ro_cells_image rsegs mm 66466 scene_init HMI' ltac:(vm_compute; reflexivity)
                          ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia)) as [_ X];
              cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X);
        assert (DI : 66466 + 50 <= bv_unsigned sp + -90 \/ bv_unsigned sp + -90 + 50 <= 66466)
          by (destruct (wr_ro_disj mm (bv_unsigned sp + -90) 50 66466 scene_init HMI' (proj2 IFT)
                          (ro_bytes_b_sound rsegs scene_init 66466 ltac:(vm_compute; reflexivity))
                          ltac:(lia) ltac:(change (length scene_init) with 50%nat; lia) ltac:(lia)) as [D|D];
              change (length scene_init) with 50%nat in D; lia)
      end.
      call MEMC.
      { bytes_by HI. }
      { reflexivity. }
      { rewrite UF90, U50. change (Z.to_nat 50) with 50%nat. exact IFT. }
      { rewrite ?unsigned_lit_wrap. lia. }
      { assumption. }
      match goal with
      | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -90))) _ |- _ =>
          rewrite UF90, U50 in P; change (Z.to_nat 50) with 50%nat in P; rename P into IFT
      end.
      apply (rw_cells_split_CB rsegs _ _ [] 50 scene_init [] [16; 34]%nat) in IFT; [|reflexivity].
      cbn [app mk_CB_cells] in IFT.
      split_first IFT (bv_unsigned sp + -90) (bv_unsigned sp + -74) II.
      rename IFT into FTa.
      change (firstn 16 scene_init) with init_hd in II.
      zr_until 121048.
      call MEMC.
      { exact HBK. }
      { reflexivity. }
      { rewrite UF74, U34. change (Z.to_nat 34) with 34%nat. exact FTa. }
      { rewrite UF74, U34. lia. }
      { assumption. }
      match goal with
      | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -74))) _ |- _ =>
          rewrite UF74, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
      end.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
      pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
      pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
      cbn [cells_bytes cbytes app firstn skipn] in BC.
      replace (bv_unsigned sp + -74 + Z.of_nat 2) with (bv_unsigned sp + -90 + 18) in BC by lia.
      clear IF.
      zr_until 88856.
      lazymatch type of ST with stk _ ?mm _ _ =>
        destruct (stk_split rsegs mm lo (bv_unsigned sp + -128 - 80) (bv_unsigned sp + -128) ST ltac:(lia)) as [STa STb]
      end.
      clear ST.
      match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { lia. }
      { lia. }
      { lia. }
      { lia. }
      { Z.div_mod_to_equations. lia. }
      { lia. }
      { exact STb. }
      { assumption. }
      { reflexivity. }
      { intros _. lia. }
      { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
        eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
      { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
      intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
      unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -128) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mo ?mn =>
        transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
        try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
      end.
      destruct PO as [STp PO].
      specialize (PO ltac:(lia)).
      pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
      replace (ret_pc (Z_to_bv 64 87808)) with (Z_to_bv 64 87808) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -128) [CB 36 (snd (ctrlparse 50 ?FB))] =>
        assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
        apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                      CB 2 [Z_to_bv 8 24; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                      CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
        [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
        rename PO into PP2
      end.
      zr_until 87988.
      match type of BC with bytes_at _ _ _ ?L =>
        eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -90) (bs := L);
                         [lia | lia | reflexivity | reflexivity | exact BC] | ]
      end.
      intros ms' PO. destruct PO as (a1' & a2' & a3' & a4' & a5' & EM). subst ms'.
      replace (ret_pc (Z_to_bv 64 87860)) with (Z_to_bv 64 87860) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      match goal with |- context [blocksum ?L] =>
        assert (BSUM : blocksum L = 0)
          by (unfold blocksum; cbn [psum nth];
              match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                replace X with Y by lia; exact SUM end end);
        rewrite BSUM
      end.
      cbn [Z.eqb].
      zstep. res_if.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -74) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -90) _ _ GG ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -92) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as FR.
      clear J1 J2 J3 SV FT2 II GG PP2.
      cbn [app] in FR.
      do 6 zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      finish.
Qed.
