(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Create HintDb asfr.

(* [comment removed for export] *)
Abbreviation AIMGLO := 0x10000%Z.
Abbreviation AIMGHI := 0x663000%Z.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hideW (P : Prop) : Prop := P.
Ltac hidehypW H := lazymatch type of H with ?T => change T with (hideW T) in H end.
(* [comment removed for export] *)
Ltac hlia := repeat match goal with |- _ /\ _ => split end;
             first [ assumption
                   | lazymatch goal with |- hideW _ => unfold hideW in *; tauto | |- _ => first [ lia | unfold hideW in *; lia ] end ].
Ltac hlia0 := unfold hideW in *; lia.
(* [comment removed for export] *)
Notation "'TSIDE' T" := (hideW (((T + 4096 <= AIMGLO)%Z \/ (AIMGHI <= T)%Z) /\ ((T + 4096 <= 0x7fff7000)%Z \/ (0x10007fff8000 <= T)%Z))) (at level 10, T at level 9).
Notation "'PSIDE' p n" := (hideW ((p + n <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= p)%Z)) (at level 10, p at level 9, n at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Lemma v_and_m1_l : forall x : word, v_and (Z_to_bv 64 18446744073709551615) x = x.
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). apply bv_eq. rewrite (u_Z2bv 18446744073709551615) by lia.
  rewrite Z.land_comm. change 18446744073709551615%Z with (2 ^ 64 - 1)%Z.
  rewrite land_ones_mod by lia. rewrite u_Z2bv; rewrite ?Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m4_aligned : forall x : word, (bv_unsigned x mod 4 = 0)%Z -> v_andi x (-4) = x.
Proof using.
  intros x Hx. pose proof (u64_range x) as R.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite andi_m4 by lia. rewrite Hx, Z.sub_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma v_sllw_mult32 : forall (c : Z) (y : word), (0 <= c < 2 ^ 31)%Z -> (bv_unsigned y mod 32 = 0)%Z ->
  v_sllw (Z_to_bv 64 c) y = Z_to_bv 64 c.
Proof using.
  intros c y Hc Hy. (lazymatch goal with |- ?G => let G' := eval unfold v_sllw in G in change_no_check G' end). rewrite Hy, Z.shiftl_0_r, u_Z2bv by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.


(* [comment removed for export] *)
Lemma rdn1_wbytes_in : forall segs m (a : word) bs (k : nat),
  (k < length bs)%nat -> (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) (at_ a (Z.of_nat k)) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof using.
  intros segs m a bs k Hk Hnw. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
  rewrite (AsRtIMemmove.wbytes_get_g bs m a (at_ a (Z.of_nat k)) Hnw).
  rewrite at_u by lia.
  replace (inrng (bv_unsigned a) (Z.of_nat (length bs)) (bv_unsigned a + Z.of_nat k)) with true.
  2:{ symmetry. apply inrng_true. lia. }
  replace (Z.to_nat (bv_unsigned a + Z.of_nat k - bv_unsigned a)) with k by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma shad_facts2 : forall p n8, (p + n8 <= 0x7fff7000 \/ 0x10007fff8000 <= p)%Z -> (0 <= p)%Z -> (p + n8 <= 2 ^ 47)%Z -> (8 <= n8)%Z ->
  (p mod 8 = 0)%Z -> (n8 mod 8 = 0)%Z ->
  (((p + n8 <= 0x7fff7000 /\ p / 8 + n8 / 8 <= 0xfffee00) \/ (0x10007fff8000 <= p /\ 0x2001000 <= p / 8))
   /\ p / 8 + n8 / 8 <= 2 ^ 44 /\ 1 <= n8 / 8 /\ p = 8 * (p / 8) /\ n8 = 8 * (n8 / 8)
   /\ (p + n8 + 7) / 8 = p / 8 + n8 / 8)%Z.
Proof using. intros p n8 H0 H1 H2 H3 H4 H5. repeat split; try lia. Qed.
Lemma p16_facts : forall x, (x mod 16 = 0)%Z -> (16 <= x)%Z ->
  ((x - 16) mod 4 = 0 /\ (x + -16) mod 4 = 0 /\ (8 * (x + -16)) mod 32 = 0 /\ x mod 8 = 0 /\ (x - 16) mod 16 = 0 /\ (x + -16) mod 8 = 0)%Z.
Proof using. intros x Hx H16. repeat split; lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_wbytes_sub : forall segs m (a : word) bs (k j : nat),
  (k + j <= length bs)%nat -> (bv_unsigned a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) (at_ a (Z.of_nat k)) j = Some (firstn j (skipn k bs)).
Proof using.
  intros segs m a bs k j. revert k. induction j as [|j IH]; intros k Hkj Hnw.
  - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite firstn_O. reflexivity.
  - rewrite AsAinvDefs3.rdn_S. rewrite (rdn1_wbytes_in segs m a bs k) by lia.
    pose proof (u64_range a) as Ha.
    replace (at_ a (Z.of_nat k) + 1)%bv with (at_ a (Z.of_nat (S k))).
    2:{ apply bv_eq. rewrite u_add1 by (rewrite at_u; lia). rewrite !at_u by lia. lia. }
    rewrite (IH (S k)) by lia.
    destruct (skipn k bs) as [|b r] eqn:E.
    + exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia.
    + replace (skipn (S k) bs) with r.
      2:{ change r with (skipn 1 (b :: r)). rewrite <- E. rewrite skipn_skipn. f_equal; lia. }
      (lazymatch goal with |- ?G => let G' := eval cbn [firstn] in G in change_no_check G' end). f_equal. f_equal.
      change b with (nth 0 (b :: r) (Z_to_bv 8 0)). rewrite <- E. rewrite nth_skipn. f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_skip : forall segs m (a : word) n bs (k : nat),
  rdn segs m a n = Some bs -> (k <= n)%nat -> (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs m (at_ a (Z.of_nat k)) (n - k) = Some (skipn k bs).
Proof using.
  intros segs m a n bs k. revert a n bs. induction k as [|k IH]; intros a n bs Hr Hk Hnw.
  - (lazymatch goal with |- ?G => let G' := eval cbn [skipn Z.of_nat] in G in change_no_check G' end). rewrite at_0, Nat.sub_0_r. exact Hr.
  - destruct n as [|n]; [lia|]. rewrite AsAinvDefs3.rdn_S in Hr.
    destruct (rdn segs m a 1) as [[|b [|]]|] eqn:E1; try discriminate Hr.
    destruct (rdn segs m (a + 1)%bv n) as [r|] eqn:E2; [|discriminate Hr]. injection Hr as <-.
    pose proof (u64_range a) as Ha.
    replace (at_ a (Z.of_nat (S k))) with (at_ (a + 1)%bv (Z.of_nat k)).
    2:{ apply bv_eq. rewrite !at_u; rewrite ?u_add1 by lia; lia. }
    replace (S n - S k)%nat with (n - k)%nat by lia. (lazymatch goal with |- ?G => let G' := eval cbn [skipn] in G in change_no_check G' end).
    apply IH; [exact E2 | lia | rewrite u_add1 by lia; lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_defined_ex : forall segs (m : word -> option byte) (a : word) (n : nat),
  (forall i, (bv_unsigned a <= i < bv_unsigned a + Z.of_nat n)%Z -> m (Z_to_bv 64 i) <> None) ->
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof using.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Hdef Hnw.
  - exists []. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    destruct (m a) as [b|] eqn:E.
    2:{ exfalso. apply (Hdef (bv_unsigned a)); [lia|]. rewrite Z_to_bv_bv_unsigned. exact E. }
    destruct (IH (a + 1)%bv) as [bs [Hr Hl]].
    + intros i Hi. apply Hdef. rewrite u_add1 in Hi by lia. lia.
    + rewrite u_add1 by lia. lia.
    + rewrite Hr. exists (b :: bs). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_cat : forall segs m (a : word) (j k : nat) l1 l2,
  rdn segs m a j = Some l1 -> rdn segs m (at_ a (Z.of_nat j)) k = Some l2 -> (bv_unsigned a + Z.of_nat j + Z.of_nat k < 2 ^ 64)%Z ->
  rdn segs m a (j + k) = Some (l1 ++ l2).
Proof using.
  intros segs m a j. revert a. induction j as [|j IH]; intros a k l1 l2 H1 H2 Hnw.
  - cbn in H1. injection H1 as <-. cbn [Z.of_nat] in H2. rewrite at_0 in H2. exact H2.
  - rewrite AsAinvDefs3.rdn_S in H1. (lazymatch goal with |- ?G => let G' := eval cbn [Nat.add] in G in change_no_check G' end). rewrite AsAinvDefs3.rdn_S.
    destruct (rdn segs m a 1) as [[|b0 [|]]|] eqn:E1; try discriminate H1.
    destruct (rdn segs m (a + 1)%bv j) as [r|] eqn:E2; [|discriminate H1]. injection H1 as <-.
    pose proof (u64_range a) as Ha.
    rewrite (IH (a + 1)%bv k r l2 E2); [reflexivity | | rewrite u_add1 by lia; lia].
    replace (at_ (a + 1)%bv (Z.of_nat j)) with (at_ a (Z.of_nat (S j))); [exact H2|].
    apply bv_eq. rewrite !at_u; rewrite ?u_add1 by lia; lia.
Qed.

Lemma ret_ok_lit : forall z, (0 <= z < 2 ^ 64)%Z -> (z mod 2 = 0)%Z -> ret_ok (Z_to_bv 64 z).
Proof using. intros z Hz He. apply ret_ok_even. rewrite u_Z2bv by lia. exact He. Qed.
(* [comment removed for export] *)
Lemma wc_rdn_wbytes_out3 : forall segs bs m (addr a : word) n,
  ((bv_unsigned a + Z.of_nat n <= bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)
   /\ bv_unsigned a + Z.of_nat n <= 2^64 /\ bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof. intros segs bs m addr a n (H1 & H2 & H3). apply rdn_wbytes_out; assumption. Qed.
(* [comment removed for export] *)
Lemma wd_store_ok_sub3 : forall segs m (lo a : word) (N n : nat),
  (bv_unsigned lo + Z.of_nat N <= 2 ^ 64 /\ bv_unsigned lo <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N)%Z ->
  store_ok segs m lo N = true -> store_ok segs m a n = true.
Proof. intros segs m lo a N n (H1 & H2 & H3) H. exact (store_ok_sub segs m lo a N n H1 H H2 H3). Qed.
End FPGen1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac valz :=
  apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli, v_add, v_sub, v_addi, v_or, at_ in G in change_no_check G' end);
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; unorm; first [reflexivity | lia].

(* [comment removed for export] *)
Ltac addr_as Hr :=
  lazymatch goal with |- rdn _ _ ?a _ = _ =>
    lazymatch type of Hr with rdn _ _ ?b _ = _ =>
      first [ constr_eq a b
            | lazymatch a with Z_to_bv 64 ?x => lazymatch b with Z_to_bv 64 ?y => replace x with y by lia end end
            | replace a with b by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia) ] end end.

(* [comment removed for export] *)
Ltac rd_peel :=
  autounfold with asfr;
  repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]).

(* [comment removed for export] *)
Ltac rd_addr Hr :=
  gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
  try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; fold_at_vars);
  rd_peel; addr_as Hr; exact Hr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wc_off_ne a b :=
  lazymatch a with at_ ?x ?k1 => lazymatch b with at_ ?y ?k2 =>
    constr_eq x y; is_Z_lit k1; is_Z_lit k2;
    lazymatch eval vm_compute in (Z.eqb k1 k2) with false => idtac end end end.
Ltac rd_hit8 :=
  lazymatch goal with |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ =>
    first [ constr_eq a b
          | wc_off_ne a b; fail 1
          | replace b with a by (first [f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia]) ];
    apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia end.
(* [comment removed for export] *)
Ltac wd_hit8 :=
  lazymatch goal with |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ => constr_eq a b; apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia end.
Ltac wd_rdstep side :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b 8%nat = _ =>
      tryif constr_eq a b then first [ wd_hit8 | rewrite wc_rdn_wbytes_out3; [ | side ] ]
      else tryif wc_off_ne a b then (rewrite wc_rdn_wbytes_out3; [ | side ])
      else first [ rewrite wc_rdn_wbytes_out3; [ | side ] | rd_hit8 ]
  | _ => first [ rd_hit8 | rewrite wc_rdn_wbytes_out3; [ | side ] ]
  end.
Ltac rd_own :=
  gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; autounfold with asfr;
  repeat (wd_rdstep rd8_side);
  idtac.

(* [comment removed for export] *)
Ltac sok_side_old := rewrite ?at_u by lia; unorm; rewrite ?Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); lia.
(* [comment removed for export] *)
Ltac sok_side := first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_z2n1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); wd_zofnat; lia ]
                       | sok_side_old ].
Ltac any_ok_old :=
  repeat (eapply store_ok_mono; [apply wbytes_grows|]);
  match goal with
  | H : store_ok ?sg ?m ?b ?N = true |- store_ok _ _ _ _ = true =>
      first [ exact H
            | eapply (store_ok_sub sg m b _ N); [ sok_side | exact H | sok_side | sok_side ] ]
  end.
(* [comment removed for export] *)
Ltac sok_fast := (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_z2n1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Pos.iter_op Nat.add Nat.mul] in G in change_no_check G' end); wd_zofnat; lia.
Ltac any_ok :=
  first [ repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          match goal with
          | H : store_ok ?sg ?m ?b ?N = true |- store_ok _ _ _ _ = true =>
              first [ exact H | apply (wd_store_ok_sub3 sg m b _ N); [ solve [sok_fast] | exact H ] ]
          end
        | any_ok_old ].
Ltac stk_ok := any_ok.
Ltac hyp_ok := any_ok.

(* [comment removed for export] *)
Ltac fsd F D aa :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.
(* [comment removed for export] *)
Ltac fsw F D aa :=
  chain_step; [reflexivity
    | eapply step_sw_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac fld F D vv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
      [exact F | reflexivity | exact D | rd_own | apply bytes_le_to_Z_8]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac cld F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clw F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lw with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clwu F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lwu with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clhu F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_lhu with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D | rd_addr Hr | first [exact Hv | rewrite Hv; unorm; first [reflexivity | lia]] ]
    | step_simpl]; vn.
Ltac clbu F D bb Hr :=
  chain_step; [reflexivity
    | eapply step_lbu with (b := bb);
      [exact F | reflexivity | exact D | rd_addr Hr ]
    | step_simpl]; vn.
Ltac clb F D bb Hr :=
  chain_step; [reflexivity
    | eapply step_lb with (b := bb);
      [exact F | reflexivity | exact D | rd_addr Hr ]
    | step_simpl]; vn.
(* [comment removed for export] *)
Ltac cld8 F D vv Hr := cld F D (word_to_le_bytes 8 vv) vv Hr (bytes_le_to_Z_8 vv).

(* [comment removed for export] *)
Ltac rt F D :=
  chain_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact D | gres; rwH; reflexivity] | step_simpl]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
