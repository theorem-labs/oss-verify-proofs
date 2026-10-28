(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Stdio Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnSpecs2 BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnArith BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct AsByte RtCallA W_cryptoA W_expandA W_smallA W_topA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2029544 => 1
  | 2029548 => 2
  | 2030424 => 1
  | 2030428 => 2
  | 2030432 => 2
  | 2030436 => 2
  | 2030448 => 2
  | 2030496 => 2
  | 2030500 => 1
  | 2030504 => 1
  | 2030508 => 1
  | 2030512 => 2
  | 2030536 => 2
  | 2030588 => 2
  | 2030624 => 2
  | 2030636 => 2
  | 2030716 => 2
  | 2030732 => 2
  | 2030736 => 1
  | 2030740 => 2
  | 2030888 => 2
  | 2030896 => 2
  | 2030904 => 1
  | 2030908 => 1
  | 2030912 => 1
  | 2030916 => 2
  | 2031032 => 2
  | 2031036 => 1
  | 2031040 => 1
  | 2031044 => 1
  | 2031048 => 2
  | 2031052 => 2
  | 2031056 => 1
  | 2031060 => 2
  | 2031108 => 1
  | 2031112 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition byte_ok (c : Z) : Prop := 0 <= c < 256.

(* [comment removed for export] *)
Lemma bytes_head_read : forall m P x (l : list Z) a,
  bytes_at bsegs m P (to_bytes (x :: l)) -> a = wa P -> ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 x].
Proof.
  intros m P x l a HB ->. pose proof (bytes_at_ov_read bsegs m P _ 0 1 HB ltac:(cbn; lia)) as R.
  replace (P + Z.of_nat 0) with P in R by lia. exact R.
Qed.

Lemma bytes_tail : forall m P x (l : list Z), bytes_at bsegs m P (to_bytes (x :: l)) -> bytes_at bsegs m (P + 1) (to_bytes l).
Proof. intros m P x l HB. change (to_bytes (x :: l)) with ([Z_to_bv 8 x] ++ to_bytes l) in HB. apply bytes_at_app in HB. exact (proj2 HB). Qed.

Lemma skip_zero_bytes_nz : forall x l, x <> 0 -> skip_zero_bytes (x :: l) = x :: l.
Proof. intros x l H. destruct x; [congruence| reflexivity| reflexivity]. Qed.

Lemma skip_zero_bytes_suffix : forall l, exists z, l = z ++ skip_zero_bytes l.
Proof.
  induction l as [|x l IH]; [exists []; reflexivity|]. destruct (Z.eq_dec x 0) as [->|NE].
  - destruct IH as (z & E). exists (0 :: z). cbn [skip_zero_bytes app]. rewrite <- E. reflexivity.
  - exists []. rewrite skip_zero_bytes_nz by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma b2b_skipA : forall (l : list Z) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
  l <> [] -> Forall byte_ok l -> bytes_at bsegs m P (to_bytes l) -> Z.of_nat (length l) < 2^31 ->
  acc bsegs m P (Z.of_nat (length l)) -> 0 < P -> P + Z.of_nat (length l) <= 140737488355328 ->
  (forall a4' a5' s4', evt bsegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + Z.of_nat (length l) - Z.of_nat (length (skip_zero_bytes l))))
              (Z_to_bv 64 (P + Z.of_nat (length l) - Z.of_nat (length (skip_zero_bytes l)))) (Z_to_bv 64 1) (Z_to_bv 64 1) a4' a5' a6 a7 s2 s3 s4' (Z_to_bv 64 1)
              (Z_to_bv 64 0) (Z_to_bv 64 SHB) s8 s9 (Z_to_bv 64 (Z.of_nat (length (skip_zero_bytes l)))) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x1efc54) fc None m (seg_rom bsegs))) ->
  evt bsegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 1) a4 a5 a6 a7 s2 s3
              (Z_to_bv 64 (Z.of_nat (length l))) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x1efbfc) fc None m (seg_rom bsegs)).
Proof.
  induction l as [|x l IH]; intros until P; intros NE FB HB LEN ACC P0 PT K; [congruence|].
  inversion FB as [|? ? Hx FB']; subst. unfold byte_ok in Hx.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU.
  cbn [length] in *. rewrite Nat2Z.inj_succ in *.
  (* [comment removed for export] *)
  assert (P0' : 0 <= P) by lia.
  assert (REST : forall a4' a5', evt bsegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 1) a4' a5' a6 a7 s2 s3
              (Z_to_bv 64 (Z.succ (Z.of_nat (length l)))) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s8 s9 (Z_to_bv 64 (Z.succ (Z.of_nat (length l)))) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x1efc14) fc None m (seg_rom bsegs))).
  { intros a4' a5'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (bytes_head_read mx P x l a HB ltac:(addr_tac)) as RD end.
    step. clear RD. rewrite (zxb_small x) by lia.
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by lia.
    - (* [comment removed for export] *)
      rewrite (skip_zero_bytes_nz x l) in K by lia. cbn [length] in K. rewrite Nat2Z.inj_succ in K.
      replace P with (P + Z.succ (Z.of_nat (length l)) - Z.succ (Z.of_nat (length l))) at 1 2 by lia. eapply K.
    - assert (x = 0) by lia. subst x. change (skip_zero_bytes (0 :: l)) with (skip_zero_bytes l) in K.
      step. setreg 11%Z (Z_to_bv 64 (P + 1)) ltac:(f_equal; lia).
      ub. do 2 step. ub.
      step.
      step. rewrite (swrap32_wrap64 (Z.succ (Z.of_nat (length l))) (-1)) by lia.
      replace (Z.succ (Z.of_nat (length l)) + -1) with (Z.of_nat (length l)) by lia.
      step. if_cases KL; zify_cond KL; rewrite ?signed_small in KL by lia.
      + (* [comment removed for export] *)
        eapply IH; [destruct l; [cbn in KL; lia| discriminate]| exact FB'| eapply bytes_tail; exact HB| lia
                   | eapply acc_sub; [exact ACC| lia| lia] | lia | lia |].
        intros a4'' a5'' s4''.
        replace (P + 1 + Z.of_nat (length l) - Z.of_nat (length (skip_zero_bytes l)))
          with (P + Z.succ (Z.of_nat (length l)) - Z.of_nat (length (skip_zero_bytes l))) by lia. eapply K.
      + (* [comment removed for export] *)
        assert (l = []) by (destruct l; [reflexivity| cbn [length] in KL; lia]). subst l. cbn [skip_zero_bytes length] in K.
        step. step. replace (P + 1) with (P + Z.succ (Z.of_nat 0%nat) - Z.of_nat 0%nat) by lia. eapply K. }

  ub. step.
  do 2 step. shl1 sb OK.
  step.
  destruct (sh_ok_cases sb P OK) as [-> | (k & K1 & K2 & E1 & E2)].
  - rewrite sxb_z8. if_false. apply REST.
  - rewrite E1. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [|exfalso; lia]. clear KS.
    step. rewrite ?(unsigned_lit P) by lia. rewrite (land7_mod8 P) by lia.
    step. if_cases KB; zify_cond KB.
    + apply REST.
    + exfalso. rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound P 8 ltac:(lia)); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma b2b_innerA : forall (t : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t1 s0 s1 a1 a4 a5 a7 s3 s4 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Q : Z) (fl : list Z) (j : nat) (l : Z),
  bytes_at bsegs m Q (to_bytes fl) -> Forall byte_ok fl ->
  (1 <= t)%nat -> (j + t <= 8)%nat -> (t <= length fl)%nat -> (t = length fl \/ (j + t = 8)%nat) ->
  0 <= l < 2 ^ (8 * Z.of_nat j) -> Z.of_nat (length fl) < 2^31 -> 1 < Q -> Q + Z.of_nat (length fl) <= 140737488355328 ->
  acc bsegs m Q (Z.of_nat (length fl)) ->
  (forall t0' t1' t2' a0' a7' t3', evt bsegs POST
     (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1 (Z_to_bv 64 2) (Z_to_bv 64 56) a4 a5
              (Z_to_bv 64 (l + 2 ^ (8 * Z.of_nat j) * le_bytes_val (firstn t (rev fl)))) a7'
              (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1 - Z.of_nat t)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl) - Z.of_nat t)) s11 t3' t4 t5 t6)
         F (Z_to_bv 64 0x1efda4) fc None m (seg_rom bsegs))) ->
  evt bsegs POST
     (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length fl))) t1 (Z_to_bv 64 (8 * Z.of_nat j)) s0 s1 (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1)) a1
              (Z_to_bv 64 2) (Z_to_bv 64 56) a4 a5 (Z_to_bv 64 l) a7 (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1)) s3 s4
              (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length fl))) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x1efd28) fc None m (seg_rom bsegs)).
Proof.
  induction t as [|t IH]; intros until l; intros HB FB T1 JT TL TE HL LEN Q1 QH ACC K; [lia|].
  destruct (rev fl) as [|x rfl] eqn:ER; [apply (f_equal (@length Z)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
  assert (EFL : fl = rev rfl ++ [x]) by (rewrite <- (rev_involutive fl), ER; reflexivity).
  assert (LFL : length fl = S (length rfl)) by (rewrite EFL, length_app, length_rev; cbn; lia).
  assert (Hx : byte_ok x) by (rewrite EFL in FB; apply Forall_app in FB; destruct FB as [_ FB]; inversion FB; assumption).
  unfold byte_ok in Hx.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU.
  assert (RD : ov_read_bytes bsegs m (wa (Q + Z.of_nat (length rfl))) 1 = Some [Z_to_bv 8 x]).
  { rewrite EFL in HB. unfold to_bytes in HB. rewrite map_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite length_map, length_rev in HB. eapply bytes_head_read; [exact HB| reflexivity]. }
  apply hide_intro in RD.
  rewrite LFL. rewrite Nat2Z.inj_succ. replace (Q + Z.succ (Z.of_nat (length rfl)) - 1) with (Q + Z.of_nat (length rfl)) by lia.
  assert (Q0 : 0 <= Q) by lia.
  ub. step. setreg 6%Z (Z_to_bv 64 (Q + Z.of_nat (length rfl) - 1)) ltac:(f_equal; lia).
  ub. step.

  assert (REST : forall t2' t3', evt bsegs POST
     (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.succ (Z.of_nat (length rfl)))) (Z_to_bv 64 (Q + Z.of_nat (length rfl) - 1)) t2' s0 s1
              (Z_to_bv 64 (Q + Z.of_nat (length rfl))) a1 (Z_to_bv 64 2) (Z_to_bv 64 56) a4 a5 (Z_to_bv 64 l) (Z_to_bv 64 (8 * Z.of_nat j))
              (Z_to_bv 64 (Q + Z.of_nat (length rfl))) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.succ (Z.of_nat (length rfl)))) s11 t3' t4 t5 t6)
         F (Z_to_bv 64 0x1efd58) fc None m (seg_rom bsegs))).
  { intros t2' t3'. pose proof (hide_elim _ RD) as RD1.
    step. clear RD1. rewrite (zxb_small x) by lia.
    step. setreg 18%Z (Z_to_bv 64 (Q + Z.of_nat (length rfl) - 1)) ltac:(f_equal; lia).
    do 6 step.
    rewrite !(unsigned_lit x) by lia. rewrite Z.lxor_0_l.
    replace (Z.land x 255) with x by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    rewrite v_sltu_b2z. rewrite !(unsigned_lit x) by lia. rewrite Z.ltb_irrefl. cbn [Z.b2z].
    rewrite (unsigned_lit (8 * Z.of_nat j)) by lia. rewrite (Z.mod_small (8 * Z.of_nat j) 64) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    assert (WB : 1 <= 2 ^ (8 * Z.of_nat j) <= 2 ^ 56) by (split; [apply (Z.pow_le_mono_r 2 0); lia| apply Z.pow_le_mono_r; lia]).
    assert (W8 : 2 ^ (8 * Z.of_nat (S j)) = 256 * 2 ^ (8 * Z.of_nat j)).
    { replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    set (W := 2 ^ (8 * Z.of_nat j)) in *.
    rewrite (unsigned_lit (x * W)) by nia. rewrite (unsigned_lit l) by lia.
    rewrite (lor_disjoint (x * W) l (8 * Z.of_nat j)); [| lia | fold W; lia | fold W; apply Z.mod_mul; lia].
    step. rewrite (swrap32_wrap64 (Z.succ (Z.of_nat (length rfl))) (-1)) by lia.
    replace (Z.succ (Z.of_nat (length rfl)) + -1) with (Z.of_nat (length rfl)) by lia.
    assert (EXIT : forall t0' t1' t2x a0' a7' t3x, (t = 0%nat \/ (j + 1)%nat = 8%nat) -> evt bsegs POST
       (MS (mkR ra sp gp tp t0' t1' t2x s0 s1 a0' a1 (Z_to_bv 64 2) (Z_to_bv 64 56) a4 a5 (Z_to_bv 64 (x * W + l)) a7'
                (Z_to_bv 64 (Q + Z.of_nat (length rfl) - 1)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                (Z_to_bv 64 (Z.of_nat (length rfl))) s11 t3x t4 t5 t6)
           F (Z_to_bv 64 0x1efda4) fc None m (seg_rom bsegs))).
    { intros t0' t1' t2x a0' a7' t3x HT.
      assert (t = 0%nat) by lia. subst t. cbn [firstn le_bytes_val] in K. rewrite (Z.mod_small x 256) in K by lia.
      replace (l + W * (x + 256 * 0)) with (x * W + l) in K by lia.
      replace (Q + Z.of_nat (length fl) - 1 - Z.of_nat 1) with (Q + Z.of_nat (length rfl) - 1) in K by lia.
      replace (Z.of_nat (length fl) - Z.of_nat 1) with (Z.of_nat (length rfl)) in K by lia.
      eapply K. }
    step. if_cases KR; zify_cond KR; rewrite ?signed_small in KR by lia.
    - (* [comment removed for export] *)
      apply EXIT. lia.
    - do 3 step. step. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
      + (* [comment removed for export] *)
        assert (T1' : (1 <= t)%nat) by lia.
        replace (8 * Z.of_nat j + 8) with (8 * Z.of_nat (S j)) by lia.
        replace (Q + Z.of_nat (length rfl) - 1) with (Q + Z.of_nat (length (rev rfl)) - 1) by (rewrite length_rev; lia).
        replace (Z.of_nat (length rfl)) with (Z.of_nat (length (rev rfl))) by (rewrite length_rev; lia).
        eapply (IH POST) with (fl := rev rfl) (j := S j) (l := x * W + l);
          [ rewrite EFL in HB; unfold to_bytes in HB; rewrite map_app in HB; apply bytes_at_app in HB; exact (proj1 HB)
          | rewrite EFL in FB; apply Forall_app in FB; exact (proj1 FB)
          | exact T1' | lia | rewrite length_rev; lia | rewrite length_rev; lia
          | rewrite W8; fold W; nia | rewrite length_rev; lia | exact Q1 | rewrite length_rev; lia
          | eapply acc_sub; [exact ACC | lia | rewrite length_rev; lia] | ].
        intros t0' t1' t2y a0' a7' t3y. rewrite rev_involutive, W8. fold W.
        cbn [firstn le_bytes_val] in K. rewrite (Z.mod_small x 256) in K by lia.
        replace (x * W + l + 256 * W * le_bytes_val (firstn t rfl)) with (l + W * (x + 256 * le_bytes_val (firstn t rfl))) by ring.
        replace (Q + Z.of_nat (length (rev rfl)) - 1 - Z.of_nat t) with (Q + Z.of_nat (length fl) - 1 - Z.of_nat (S t)) by (rewrite length_rev; lia).
        replace (Z.of_nat (length (rev rfl)) - Z.of_nat t) with (Z.of_nat (length fl) - Z.of_nat (S t)) by (rewrite length_rev; lia).
        eapply K.
      +   step. apply EXIT. lia. }

  ub. do 2 step. shl1 sb OK. step.
  destruct (sh_ok_cases sb (Q + Z.of_nat (length rfl)) OK) as [-> | (k & K1 & K2 & E1 & E2)].
  - rewrite sxb_z8. if_false. apply REST.
  - rewrite E1. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [|exfalso; lia]. clear KS.
    step. rewrite ?(unsigned_lit (Q + Z.of_nat (length rfl))) by lia. rewrite (land7_mod8 (Q + Z.of_nat (length rfl))) by lia.
    step. if_cases KB; zify_cond KB.
    + exfalso. rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound (Q + Z.of_nat (length rfl)) 8 ltac:(lia)); lia). lia.
    + step. apply REST.
Qed.

Lemma upd_app_mid' : forall {X} (l1 : list X) x l2 v, Arr.upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|y l1 IH]; intros x l2 v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma b2b_outerA : forall (k : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 a0 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (v1 v2 v3 v4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (Q D A : Z) (fl pre rest : list Z),
  bytes_at bsegs m Q (to_bytes fl) -> Forall byte_ok fl ->
  8 * Z.of_nat k < Z.of_nat (length fl) <= 8 * Z.of_nat k + 8 -> Z.of_nat (length fl) < 2^31 -> 1 < Q -> Q + Z.of_nat (length fl) <= 140737488355328 ->
  u64arr bsegs m D (wlimbs (pre ++ rest)) -> (S k <= length rest)%nat -> Z.of_nat (length (pre ++ rest)) < 2^31 ->
  (D + 8 * Z.of_nat (length (pre ++ rest)) <= Q \/ Q + Z.of_nat (length fl) <= D) ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 D); C4 v1; C4 v2; C4 v3; C4 v4] -> (A + 24 <= D \/ D + 8 * Z.of_nat (length (pre ++ rest)) <= A) -> 0 < D ->
  munch [(D, D + 8 * Z.of_nat (length (pre ++ rest)))] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  acc bsegs m0 Q (Z.of_nat (length fl)) -> acc bsegs m0 D (8 * Z.of_nat (length (pre ++ rest))) -> D mod 8 = 0 ->
  acc bsegs m0 A 24 -> A mod 8 = 0 -> 0 <= A -> A + 24 <= 140737488355328 ->
  0 <= D -> D + 8 * Z.of_nat (length (pre ++ rest)) <= 140737488355328 -> offshW [(D, D + 8 * Z.of_nat (length (pre ++ rest)))] ->
  (forall t0' t1' t2' a0' a1' a5' a6' a7' s2' s10' s11' t3' m',
     u64arr bsegs m' D (wlimbs (pre ++ bytes_to_limbs (S k) (rev fl) ++ skipn (S k) rest)) ->
     munch [(D, D + 8 * Z.of_nat (length (pre ++ rest)))] m0 m' -> wmono bsegs m0 m' -> mem_inv bsegs m' ->
     evt bsegs POST
       (MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' a1' (Z_to_bv 64 2) (Z_to_bv 64 56) (Z_to_bv 64 (shad A)) a5' a6' a7'
                s2' s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s10' s11' t3' t4 t5 t6)
           F (Z_to_bv 64 0x1efdf8) fc None m' (seg_rom bsegs))) ->
  evt bsegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 (Z_to_bv 64 (Z.of_nat (length pre))) (Z_to_bv 64 2) (Z_to_bv 64 56) (Z_to_bv 64 (shad A)) a5 a6 a7
              (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl))) (Z_to_bv 64 (Z.of_nat k)) t3 t4 t5 t6)
         F (Z_to_bv 64 0x1efd10) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until rest; intros HB FB KL LEN Q1 QH U KR LPR DJ RDD DJA D0 MU WM MI ACCQ ACCD ALD ACCA ALA A0 A47 D00 DT OFF K.
  all: assert (ACCQm : acc bsegs m Q (Z.of_nat (length fl))) by (eapply (acc_munch bsegs _ m0 m _ _ ACCQ MU OFF); lia).
  all: pose proof (u64arr_bound bsegs m D _ U) as UB; rewrite wlimbs_len in UB.
  all: step; step; (if_cases KZ; zify_cond KZ; [exfalso; apply andb_false_iff in KZ; destruct KZ as [KZ|KZ]; apply Z.ltb_ge in KZ; lia|]); try clear KZ0 KZ1.
  all: do 4 step.
  all: replace (Z_to_bv 64 (Z.of_nat 0)) with (Z_to_bv 64 0) by reflexivity.
  - (* [comment removed for export] *)
    eapply (b2b_innerA (length fl) POST) with (fl := fl) (j := 0%nat) (l := 0);
      [exact HB| exact FB| lia| lia| lia| left; reflexivity| cbn; lia| exact LEN| exact Q1| exact QH| exact ACCQm|].
    intros t0' t1' t2' a0' a7' t3'. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.mul_1_l, Z.add_0_l.
    replace (firstn (length fl) (rev fl)) with (rev fl) by (symmetry; rewrite <- (length_rev fl); apply firstn_all).
    shl. chk0.
    destruct rest as [|r0 rest']; [cbn in KR; lia|].
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ r0 :: rest')))) by (rewrite wlimbs_len, length_app; cbn [length]; lia).
    assert (LPR' : Z.of_nat (length (pre ++ r0 :: rest')) = Z.of_nat (length pre) + 1 + Z.of_nat (length rest')) by (rewrite length_app; cbn [length]; lia).
    step. do 2 step.
    rewrite (unsigned_lit (Z.of_nat (length pre))) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (D + Z.of_nat (length pre) * 2 ^ 3) with (D + 8 * Z.of_nat (length pre)) by lia.
    ub. do 2 step. shl. chk0.
    pose proof (u64arr_store_ok bsegs m D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW.
    pose proof (u64arr_write bsegs m D _ (Z.of_nat (length pre)) (Z_to_bv 64 (le_bytes_val (rev fl))) U IDX) as U2.
    step. store_done.
    step. step. step. if_false.
    eapply K; [| exact MU| exact WM| exact MI].
    rewrite Nat2Z.id in U2. unfold wlimbs in U2. rewrite map_app in U2. cbn [map] in U2.
    rewrite <- (length_map (fun x : Z => Z_to_bv 64 x) pre) in U2. rewrite upd_app_mid' in U2.
    cbn [bytes_to_limbs skipn app]. unfold wlimbs. rewrite map_app. cbn [map].
    rewrite firstn_all2 by (rewrite length_rev; lia). exact U2.
  - (* [comment removed for export] *)
    eapply (b2b_innerA 8 POST) with (fl := fl) (j := 0%nat) (l := 0);
      [exact HB| exact FB| lia| lia| lia| right; reflexivity| cbn; lia| exact LEN| exact Q1| exact QH| exact ACCQm|].
    intros t0' t1' t2' a0' a7' t3'. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.mul_1_l, Z.add_0_l.
    shl. chk0.
    destruct rest as [|r0 rest']; [cbn in KR; lia|].
    set (v := le_bytes_val (firstn 8 (rev fl))) in *.
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ r0 :: rest')))) by (rewrite wlimbs_len, length_app; cbn [length]; lia).
    assert (LTB : length (to_bytes fl) = length fl) by (unfold to_bytes; apply length_map).
    assert (LPR' : Z.of_nat (length (pre ++ r0 :: rest')) = Z.of_nat (length pre) + 1 + Z.of_nat (length rest')) by (rewrite length_app; cbn [length]; lia).
    step. do 2 step.
    rewrite (unsigned_lit (Z.of_nat (length pre))) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (D + Z.of_nat (length pre) * 2 ^ 3) with (D + 8 * Z.of_nat (length pre)) by lia.
    ub. do 2 step. shl. chk0.
    pose proof (u64arr_store_ok bsegs m D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW.
    pose proof (u64arr_write bsegs m D _ (Z.of_nat (length pre)) (Z_to_bv 64 v) U IDX) as U2.
    step. store_done.
    step. step. rewrite (swrap32_wrap64 (Z.of_nat (S k)) (-1)) by lia.
    step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [|exfalso; lia]. clear KB.
    set (fl' := firstn (length fl - 8) fl).
    assert (LFL' : length fl' = (length fl - 8)%nat) by (subst fl'; rewrite length_firstn; lia).
    assert (EFL : fl = fl' ++ skipn (length fl - 8) fl) by (subst fl'; symmetry; apply firstn_skipn).
    assert (ELEN : length ((pre ++ [v]) ++ rest') = length (pre ++ r0 :: rest')) by (rewrite !length_app; cbn [length]; lia).
    replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [v]))) by (rewrite length_app; cbn [length]; lia).
    replace (Q + Z.of_nat (length fl) - 1 - Z.of_nat 8) with (Q + Z.of_nat (length fl') - 1) by lia.
    replace (Z.of_nat (length fl) - Z.of_nat 8) with (Z.of_nat (length fl')) by lia.
    replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    eapply (IH POST) with (m0 := m0) (D := D) (fl := fl') (pre := pre ++ [v]) (rest := rest');
      [ rewrite EFL in HB; unfold to_bytes in HB; rewrite map_app in HB; apply bytes_at_app in HB; exact (proj1 HB)
      | rewrite EFL in FB; apply Forall_app in FB; exact (proj1 FB)
      | lia | lia | exact Q1 | lia
      | | cbn [length] in KR; lia | rewrite ELEN; exact LPR | rewrite ELEN, LFL'; clear - DJ KL; lia
      | exact RDD | rewrite ELEN; exact DJA | exact D0
      | rewrite ELEN; exact MU | exact WM | eassumption
      | eapply acc_sub; [exact ACCQ | lia | lia] | rewrite ELEN; exact ACCD | exact ALD
      | exact ACCA | exact ALA | exact A0 | exact A47 | exact D00 | rewrite ELEN; exact DT | rewrite ELEN; exact OFF | ].
    + rewrite Nat2Z.id in U2. unfold wlimbs in U2. rewrite map_app in U2. cbn [map] in U2.
      rewrite <- (length_map (fun x : Z => Z_to_bv 64 x) pre) in U2. rewrite upd_app_mid' in U2.
      unfold wlimbs. rewrite <- app_assoc, map_app. cbn [map app]. exact U2.
    + intros t0'' t1'' t2'' a0'' a1' a5' a6' a7'' s2' s10' s11' t3'' m' UF MUF WMF MIF.
      eapply K; [| rewrite ELEN in MUF; exact MUF| exact WMF| exact MIF].
      cbn [bytes_to_limbs skipn]. fold v. rewrite skipn_rev. fold fl'.
      rewrite <- app_assoc in UF. cbn [app] in UF. exact UF.
Qed.

(* [comment removed for export] *)
Definition BN_BIN2BN : Z := 0x1efaac.
Definition BIN2BN : Z := 0x1efad4.
Definition BN_BIN2BN_STACK : Z := 112 + BN_EXPAND2_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_bb_tail := (E_BN_bin2bn_1f4620 : uk_tail BN_BIN2BN BIN2BN).
Local Notation E_bb_expand := (E_bin2bn_1f4850 : uk_call BIN2BN 0x1efcc8 BN_EXPAND2).

(* [comment removed for export] *)
Lemma client_block_disj : forall Σ (OW LB : list block) m q A n bk,
  AHEAP Σ OW LB m -> In (q, A, n) OW -> In bk LB -> A + n <= blk_addr bk \/ blk_addr bk + blk_size bk <= A.
Proof.
  intros Σ OW LB m q A n bk HEAP Hq Hb. pose proof (AH_nodup _ _ _ _ HEAP) as ND.
  assert (NE : blk_id (q, A, n) <> blk_id bk).
  { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id (q, A, n)) ND); [apply in_map; exact Hq| rewrite E; apply in_map; exact Hb]. }
  pose proof (AH_disjoint_gen _ _ _ _ (q, A, n) bk HEAP ltac:(apply in_or_app; left; exact Hq) ltac:(apply in_or_app; right; exact Hb) NE) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. cbn [blk_addr blk_size fst snd]. lia.
Qed.

(* [comment removed for export] *)
Definition bn_arr_w (OW : list block) (D : Z) (b : bignum bptr) : Prop :=
  match bn_d b with Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) OW | None => D = 0 /\ bn_buf b = [] end.
Lemma bn_arr_w_of : forall m OW D b, bn_arr m OW D b -> bn_arr_w OW D b.
Proof. intros m OW D b H. unfold bn_arr, bn_arr_w in *. destruct (bn_d b); [exact (proj1 H) | exact H]. Qed.

Definition BN_bin2bn_walkA_stmt : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (r : bnref) (a : Z) (SRC : Z) (bs : list Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_BIN2BN_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_BIN2BN (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD r a ->
  bytes_at bsegs m SRC (to_bytes bs) -> Forall byte_ok bs -> Z.of_nat (length bs) < 2^31 -> 0 < SRC ->
  (bs = [] \/ exists bk, In bk LB /\ blk_addr bk <= SRC /\ SRC + Z.of_nat (length bs) <= blk_addr bk + blk_size bk) ->
  a0 = wz SRC -> a1 = wz (Z.of_nat (length bs)) -> a2 = wz a ->
  (bs <> [] -> 1 < SRC) ->
  implA (BN_bin2bn (tree_ops bptr) bs r ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
              (fun _ _ OW' a0' => a0' = wz a /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_BIN2BN) fc None m (seg_rom bsegs)).

Lemma BN_bin2bn_walkA : BN_bin2bn_walkA_stmt.
Proof.
  intros until bs. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) UW CTX -> HA HB FB LEN SRC0 HBK -> -> -> SRC1.
  unfold BN_BIN2BN_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_BIN2BN, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qx & Ax & nx & Eqx & Hinx & Rx1 & Rx2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinx) as (XA0 & XA16 & _ & XAC & XAI).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (ref_at_al8 _ _ _ _ _ _ _ _ HEAP ADB HA) as AL.
  assert (INX : In (qx, Ax, nx) (OW ++ LB)) by (apply in_or_app; left; exact Hinx).
  pose proof (AH_acc_in _ _ _ _ (qx, Ax, nx) a 24 HEAP INX Rx1 Rx2) as ACC.
  pose proof (AH_offsh _ _ _ _ (qx, Ax, nx) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. unfold SHLO, SHHI in OX.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 144, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply hide_intro in HB. rename HB into HBH.
  lazymatch goal with |- implA _ _ ?Q0 _ => set (QQ := Q0) end.
  apply implA_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 8 step. release_frame FR ST (bv_unsigned sp). step. step.
  (* [comment removed for export] *)
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 step.
  step. if_cases KN; zify_cond KN; [exfalso; lia|]. clear KN.
  do 8 step. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear KA.
  do 2 step.
  (* [comment removed for export] *)
  assert (FINT : forall (Σ1 : rts RT) (ls1 : lstate bptr) (m2 : mem) (OW2 : list block) (Dr : Z)
                        (mF : mem) (nb : list Z) (top' : nat) (neg' : bool) (l3 h3 slo : Z)
                        (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
                        (F2 : bvmap 5 word) (fc2 : bv 32),
    AHEAP Σ1 OW2 LB m2 -> lib_state_h [r] ls1 m2 OW2 AD EA -> ref_at ls1 OW2 AD r a ->
    ax_pres LB (bv_unsigned sp) LIBW_A m m2 -> rt_credit RT Σ - MC <= rt_credit RT Σ1 -> cnt_eq ls OW ls1 OW2 -> refs_stable ls OW ls1 OW2 AD ->
    (forall q A n, In (q, A, n) OW -> bn_d (getbn r ls) <> Some q -> In (q, A, n) OW2) ->
    bn_arr_w OW2 Dr (getbn r ls1) -> bn_okm (getbn r ls1) ->
    w_lib OW2 lo (bv_unsigned sp) (l3, h3) -> w_okc OW2 LB ls1 AD EA false [r] (l3, h3) ->
    length nb = bn_dmax (getbn r ls1) -> limbs nb -> (top' <= length nb)%nat ->
    u64arr bsegs mF Dr (wlimbs nb) ->
    rw_cells bsegs mF a [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat top')); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax (getbn r ls1))));
                         C4 (Z_to_bv 64 (Z.b2z neg')); C4 (Z_to_bv 64 (bn_flags (getbn r ls1)))] ->
    rw_cells bsegs mF (bv_unsigned sp + -112) [CB 8 (take 8 junk0); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mF lo (bv_unsigned sp + -112) -> mem_inv bsegs mF -> lo <= slo <= bv_unsigned sp - 112 ->
    munch [(slo, bv_unsigned sp); (a, a + 24); (l3, h3)]%Z m2 mF -> wmono bsegs m2 mF ->
    evt bsegs (fun ms' => implA (TRet (tt, setbn r (mkBN (bn_d (getbn r ls1)) nb top' neg' (bn_flags (getbn r ls1))) ls1)) Σ1 QQ ms')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F2 (Z_to_bv 64 0x1efe34) fc2 None mF (seg_rom bsegs))).
  { intros Σ1 ls1 m2 OW2 Dr mF nb top' neg' l3 h3 slo x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F2 fc2
           HEAP2 LSH HA2 AXP2 CR2 CNT2 RST2 BST ARR2 OKB HW3L HW3K Lnb LMnb TOPB UF BNF FRF STF MIF SLO MUF WMF.
    clear MU WM MI ST FR OFF ACC SHB1 SHB2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_h_parts _ _ _ _ _ _ LSH) as (IDS2 & ADB2 & ERRB2 & SOK2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSH HA2) as HV2.
    destruct (ref_at_inb _ _ _ _ _ ADB2 HA2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
    set (br := getbn r ls1) in *.
    do 14 step. release_frame FRF STF (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    apply evt_done. apply implA_ret.
    assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(slo, bv_unsigned sp); (a, a + 24); (l3, h3)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (qx2, Ax2, nx2); cbn; auto|]. constructor; [exact HW3L| constructor]. }
    assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [r]) [(slo, bv_unsigned sp); (a, a + 24); (l3, h3)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
      constructor; [eapply (w_struct OW2 LB ls1 AD EA false [r] _ r a); [left; reflexivity| exact HA2| cbn; lia| cbn; lia]|].
      constructor; [exact HW3K| constructor]. }
    destruct OKB as (OKq1 & OKq2 & OKq3 & OKq4).
    unfold QQ, bn_postA. do 17 eexists. exists mG, OW2. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA r a); [| exact ND2| exact HA2| | |].
      - exact (lib_state_frame Σ1 LB [r] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MUF WMF WOK3).
      - exists Dr. split.
        + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNF.
        + unfold bn_arr, bn_arr_w, bn_dmax in *. cbn [bn_d bn_buf]. rewrite Lnb. destruct (bn_d br) as [pr|]; [split; [exact ARR2| exact UF]|].
          destruct ARR2 as [ED Eb]. split; [exact ED|]. rewrite Eb in Lnb. cbn in Lnb. destruct nb; [reflexivity| discriminate].
      - unfold bn_okm, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
        split; [exact LMnb|]. split; [lia|]. split; [exact OKq3| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS2| exact HV2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
    split; [exact STF|]. split; [exact MIF|].
    split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP2 MUF HWL3 CEIL ltac:(lia))|].
    split; [exact CR2|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn r _ ls1 OW2 OW2 HV2). fold br. rewrite CNT2.
             unfold bn_blocks. cbn [bn_d]. destruct (bn_d br); cbn [length]; lia. }
    split. { intros r' a' HA'. apply ref_at_setbn. apply RST2. exact HA'. }
    split; [reflexivity| exact BST]. }
  (* [comment removed for export] *)
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((Dr & BNr & ARRr) & OKB & LSH).
  pose proof OKB as (OKq1 & OKq2 & OKq3 & OKq4).
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r Dr HV ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
  pose proof (DSEPr r a HA) as SEPrr. clear DSEPr.
  set (br := getbn r ls) in *.
  unfold bn_cells in BNr. unfold BN_WORDS_MAX in OKq3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch type of MU with munch ?W0 _ _ =>
    apply (rw_cells_transport bsegs W0 m m1 a) in BNr; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; unfold BnHeapA.ACEIL in *; lia];
    apply (u64arr_transport bsegs W0 m m1 Dr) in Ur; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LENr; unfold BnHeapA.ACEIL in *; lia] end.
  unfold BN_bin2bn, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. fold br.
  assert (HWLa : w_lib OW lo (bv_unsigned sp) (a, a + 24)) by (right; exists (qx, Ax, nx); cbn; auto).
  assert (HWKa : w_okc OW LB ls AD EA false [r] (a, a + 24)) by (eapply (w_struct OW LB ls AD EA false [r] _ r a); [left; reflexivity| exact HA| cbn; lia| cbn; lia]).
  assert (AXP0 : ax_pres LB (bv_unsigned sp) LIBW_A m m) by apply ax_pres_refl.
  assert (CR0 : rt_credit RT Σ - MC <= rt_credit RT Σ) by (unfold MC; lia).
  step. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by lia.
  - (* [comment removed for export] *)
    assert (bs = []) by (destruct bs; [reflexivity| cbn [length] in KL; lia]). subst bs.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    apply (munch_weaken _ [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]%Z) in MU;
      [| intros x Hx; cbn [outside fst snd] in *; destruct Hx as (X1 & _); split; [exact X1| exact I]].
    clear OFF. assert (OFF : offshW [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
    do 2 step.
    remember (Z_to_bv 64 0x1efb94) as ra1 eqn:Era1.

    carve_frame 32%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    do 6 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear KA.
    step. ub. do 3 step.
    do 2 step. shl. chk0.
    step. unfold MallocRep.wz at 1.
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (unfold BnHeapA.ACEIL in *; lia).
    + (* [comment removed for export] *)
      assert (EB : bn_buf br = []).
      { unfold bn_arr in ARRr. destruct (bn_d br) as [pd|]; [|exact (proj2 ARRr)].
        exfalso. pose proof (AH_range _ _ _ _ _ _ _ HEAP (proj1 ARRr)) as (P0 & _). lia. }
      assert (ED0 : bn_dmax br = 0%nat) by (unfold bn_dmax; rewrite EB; reflexivity).
      unfold MallocRep.wz in *.
      step. do 2 step. shl. chk0. step.
      step. do 2 step. shl. chk0. step.
      do 4 step. release_frame FR0 ST (bv_unsigned sp + -112). subst ra1. step. step.
      try rewrite (ret_pc_even 0x1efb94) by lia. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (FINT Σ ls m OW Dr mx (repeat 0 (bn_dmax br)) 0%nat false a (a + 24) (bv_unsigned sp - 144));
          [exact HEAP| exact LSH| exact HA| exact AXP0| exact CR0| apply cnt_eq_refl| apply refs_stable_refl
          | intros q0 A0 n0 Hq0 _; exact Hq0| exact (bn_arr_w_of _ _ _ _ ARRr)| exact OKB| exact HWLa| exact HWKa
          | apply repeat_length| rewrite ED0; constructor| lia
          | rewrite ED0; cbn [repeat]; rewrite EB in Ur; exact Ur | exact BNr| exact FR| exact ST| exact MI| lia| exact MU| exact WM] end.
    + (* [comment removed for export] *)
      assert (HDr : exists pd, bn_d br = Some pd /\ In (pd, Dr, 8 * Z.of_nat (bn_dmax br)) OW).
      { unfold bn_arr in ARRr. destruct (bn_d br) as [pd|]; [exists pd; split; [reflexivity| exact (proj1 ARRr)]| exfalso; lia]. }
      destruct HDr as (pd & Edr & Hinpd).
      pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinpd) as (PD0 & _ & _ & PDC & PDI).
      assert (INPD : In (pd, Dr, 8 * Z.of_nat (bn_dmax br)) (OW ++ LB)) by (apply in_or_app; left; exact Hinpd).
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)])
        by (constructor; [left; cbn; lia|]; constructor; [exact HWLa|]; constructor; [exact HWLa| constructor]).
      assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (apply unsigned_lit; lia).
      unfold MallocRep.wz in *.
      step. do 2 step. shl. chk0.
      step. rewrite (sx32_small (Z.of_nat (bn_dmax br))) by lia.
      step. rewrite ?(unsigned_lit (Z.of_nat (bn_dmax br))) by lia.
      replace (Z.shiftl (Z.of_nat (bn_dmax br)) 3) with (8 * Z.of_nat (bn_dmax br)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (HEAP1 : AHEAP Σ OW LB m2) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
      assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m2) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
      assert (LSH1 : lib_state_h [r] ls m2 OW AD EA).
      { eapply lib_state_frame; [exact HEAP| exact LSH| exact MU| exact WM|].
        constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [exact HWKa|]. constructor; [exact HWKa| constructor]. }
      apply evt_done.
      eapply implA_step_same.
      { eapply (OPENSSL_cleanse_cpsA) with (b := (pd, Dr, 8 * Z.of_nat (bn_dmax br))) (D := Dr) (N := 8 * Z.of_nat (bn_dmax br)) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
        - exact HEAP1.
        - rewrite ESP2. exact ST.
        - exact CEIL.
        - rewrite ESP2. unfold OPENSSL_CLEANSE_STACK, RT_STACK. lia.
        - rewrite ESP2. unfold USTACK_TOP. lia.
        - rewrite ESP2. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI.
        - exact (proj1 LSH1).
        - exact INPD.
        - lia. }
      intros ms3 PO. unfold cleanse_post in PO. rewrite ?ESP2 in PO.
      destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & AG3 & BZ & WR3).
      rewrite (ret_pc_even 0x1ef834) by lia. unfold MallocRep.wz.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG3) in BNr; [| intros x Hx; cbn in Hx; split; [right; right; exists (qx, Ax, nx); split; [exact INX | cbn; lia] | lia]].
      assert (LSH3 : lib_state_h [r] ls m3 OW AD EA).
      { eapply (lib_state_h_icall Σ LB false [r] ls m2 m3 OW AD EA _ Dr (8 * Z.of_nat (bn_dmax br)) HEAP1 LSH1 AG3).
        eapply (w_limbs OW LB ls AD EA false [r] _ r pd Dr); [left; reflexivity| exact HV| exact Edr| exact Hinpd| cbn [fst snd]; lia| cbn [fst snd]; fold br; lia]. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) LIBW_A m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ Hc]. split.
        - destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
        - intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
          + unfold BnHeapA.ACEIL in *. lia.
          + eapply (blk_not_static Σ OW LB m2 (pd, Dr, 8 * Z.of_nat (bn_dmax br)) x HEAP1 Hinpd); [cbn; lia | exact Hc].
          + pose proof (client_block_disj _ _ _ _ _ _ _ b0 HEAP1 Hinpd Hb0) as DJ. lia. }
      assert (UZ : u64arr bsegs m3 Dr (wlimbs (repeat 0 (bn_dmax br)))).
      { apply u64arr_u8arr. rewrite lbytes_repeat0. split.
        - replace (8 * bn_dmax br)%nat with (Z.to_nat (8 * Z.of_nat (bn_dmax br))) by lia. exact BZ.
        - rewrite repeat_length. replace (Z.of_nat (8 * bn_dmax br)) with (8 * Z.of_nat (bn_dmax br)) by lia. exact WR3. }
      pose proof (AH_acc_in _ _ _ _ (qx, Ax, nx) a 24 HEAP3 INX Rx1 Rx2) as ACC3.
      clear ACC MU WM OFF Ur.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m3) as MU3.
      pose proof (wmono_refl bsegs m3) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { pose proof (AH_offsh _ _ _ _ (pd, Dr, 8 * Z.of_nat (bn_dmax br)) HEAP3 INPD) as O. cbn [blk_addr blk_size fst snd] in O.
        cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      assert (LWZ : Z.of_nat (length (wlimbs (repeat 0 (bn_dmax br)))) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, repeat_length; reflexivity).
      apply implA_from_evt.
      step. do 2 step. shl. chk0. step.
      step. do 2 step. shl. chk0. step.
      do 4 step. release_frame FR0 ST3 (bv_unsigned sp + -112). subst ra1. step. step.
      try rewrite (ret_pc_even 0x1efb94) by lia. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (FINT Σ ls m3 OW Dr mx (repeat 0 (bn_dmax br)) 0%nat false Dr (Dr + 8 * Z.of_nat (bn_dmax br)) (bv_unsigned sp - 144));
          [exact HEAP3| exact LSH3| exact HA| exact AXP3| exact CR0| apply cnt_eq_refl| apply refs_stable_refl
          | intros q0 A0 n0 Hq0 _; exact Hq0| exact (bn_arr_w_of _ _ _ _ ARRr)| exact OKB
          | right; exists (pd, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpd| lia]
          | eapply (w_limbs OW LB ls AD EA false [r] _ r pd Dr); [left; reflexivity| exact HV| exact Edr| exact Hinpd| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]
          | apply repeat_length| apply limbs_repeat; exact limb_0| lia
          | eassumption | exact BNr| exact FR| exact ST3| eassumption| lia| exact MU3| exact WM3] end.
  - (* [comment removed for export] *)
    destruct bs as [|x0 bs'] eqn:EBS; [cbn [length] in KL; lia|]. cbv iota. rewrite <- EBS in *.
    assert (NEB : bs <> []) by (rewrite EBS; discriminate). specialize (SRC1 NEB).
    destruct HBK as [HBK|(bk & Hbk & BK1 & BK2)]; [congruence|].
    assert (INBK : In bk (OW ++ LB)) by (apply in_or_app; right; exact Hbk).
    pose proof (AH_range_gen _ _ _ _ bk HEAP INBK) as (BK0 & _ & _ & BKC & BKI).
    pose proof (AH_acc_in _ _ _ _ bk SRC (Z.of_nat (length bs)) HEAP INBK BK1 BK2) as ACCS.
    set (s' := skip_zero_bytes bs) in *.
    assert (LTB : length (to_bytes bs) = length bs) by (unfold to_bytes; apply length_map).
    pose proof (hide_elim _ HBH) as HB1.
    lazymatch type of MU with munch ?W0 _ _ =>
      apply (bytes_at_transport bsegs W0 m m1 SRC) in HB1; [| exact MU| cbn [disjoint_from]; rewrite LTB; unfold BnHeapA.ACEIL in *; lia] end.
    assert (ACCS1 : acc bsegs m1 SRC (Z.of_nat (length bs))) by (eapply (acc_munch bsegs _ m m1 _ _ ACCS MU OFF); unfold BnHeapA.ACEIL in *; lia).

    step. if_true. step. rewrite (swrap32_wrap64 (Z.of_nat (length bs)) (-1)) by lia. step. ub. do 4 step. step. if_true. do 3 step. do 3 step.
    setreg 21%Z (Z_to_bv 64 1) ltac:(vm_compute; reflexivity).
    setreg 18%Z (Z_to_bv 64 (SRC + Z.of_nat (length bs) - 1)) ltac:(f_equal; lia).
    eapply (b2b_skipA bs); [exact NEB| exact FB| exact HB1| exact LEN| exact ACCS1| lia| unfold BnHeapA.ACEIL in *; lia|].
    intros a4' a5' s4'. fold s'.
    destruct (skip_zero_bytes_suffix bs) as (zs & ESFX). fold s' in ESFX.
    assert (FB' : Forall byte_ok s') by (rewrite ESFX in FB; apply Forall_app in FB; exact (proj2 FB)).
    assert (LBS : length bs = (length zs + length s')%nat) by (rewrite ESFX at 1; apply length_app).
    assert (HB' : bytes_at bsegs m1 (SRC + Z.of_nat (length zs)) (to_bytes s')).
    { rewrite ESFX in HB1. unfold to_bytes in HB1. rewrite map_app in HB1. apply bytes_at_app in HB1. rewrite length_map in HB1. exact (proj2 HB1). }
    replace (SRC + Z.of_nat (length bs) - Z.of_nat (length s')) with (SRC + Z.of_nat (length zs)) by lia.
    clearbody s'. clear HB1.
    step. step. if_true.
    step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
    + (* [comment removed for export] *)
      assert (s' = []) by (destruct s'; [reflexivity| cbn [length] in KS; lia]). subst s'.
      apply (munch_weaken _ [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]%Z) in MU;
        [| intros x Hx; cbn [outside fst snd] in *; destruct Hx as (X1 & _); split; [exact X1| exact I]].
      clear OFF. assert (OFF : offshW [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
      unfold MallocRep.wz in *.
      ub. step. do 2 step. shl. chk0. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (FINT Σ ls m OW Dr mx (bn_buf br) 0%nat (bn_neg br) a (a + 24) (bv_unsigned sp - 144));
          [exact HEAP| exact LSH| exact HA| exact AXP0| exact CR0| apply cnt_eq_refl| apply refs_stable_refl
          | intros q0 A0 n0 Hq0 _; exact Hq0| exact (bn_arr_w_of _ _ _ _ ARRr)| exact OKB| exact HWLa| exact HWKa
          | reflexivity| exact OKq1| lia
          | exact Ur | exact BNr| exact FR| exact ST| exact MI| lia| exact MU| exact WM] end.
    + (* [comment removed for export] *)
      assert (LS1 : (1 <= length s')%nat) by lia.
      destruct s' as [|yb0 sb''] eqn:ES'; [cbn [length] in LS1; lia|]. cbv iota beta. rewrite <- ES' in *. fold br.
      step. rewrite (swrap32_wrap64 (Z.of_nat (length s')) (-1)) by lia.
      ub. step. do 2 step. shl. chk0.
      step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax br))) by lia.
      do 2 step.
      set (n := ((length s' - 1) / 8 + 1)%nat) in *.
      assert (EN : Z.of_nat n - 1 = (Z.of_nat (length s') - 1) / 8).
      { subst n. rewrite Nat2Z.inj_add, Nat2Z.inj_div, Nat2Z.inj_sub by lia. change (Z.of_nat 8) with 8. change (Z.of_nat 1) with 1. lia. }
      assert (NR : 1 <= Z.of_nat n /\ 8 * (Z.of_nat n - 1) < Z.of_nat (length s') <= 8 * (Z.of_nat n - 1) + 8).
      { rewrite EN. clear - LS1. pose proof (Z.div_mod (Z.of_nat (length s') - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.of_nat (length s') - 1) 8 ltac:(lia)).
        pose proof (Z.div_pos (Z.of_nat (length s') - 1) 8 ltac:(lia) ltac:(lia)). lia. }
      assert (ES10 : bv_swrap 32 (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (Z.of_nat (length s') + -1))) ≫ 3) = Z.of_nat n - 1).
      { rewrite unsigned_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite Z.mod_small by lia.
        rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. replace (Z.of_nat (length s') + -1) with (Z.of_nat (length s') - 1) by lia.
        rewrite <- EN. apply bk_swrap32_small. lia. }
      rewrite ?ES10. replace (Z.of_nat n - 1 + 1) with (Z.of_nat n) by lia.
      assert (ENdef : n = ((length s' - 1) / 8 + 1)%nat) by reflexivity.
      apply hide_intro in EN. apply hide_intro in ENdef. clearbody n.
      (* [comment removed for export] *)
      assert (CONT : forall (Σ1 : rts RT) (ls1 : lstate bptr) (m2 : mem) (OW2 : list block)
                            (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32),
        AHEAP Σ1 OW2 LB m2 -> lib_state ls1 m2 OW2 AD EA -> stk bsegs m2 lo (bv_unsigned sp + -112) -> mem_inv bsegs m2 ->
        ax_pres LB (bv_unsigned sp) LIBW_A m m2 -> rt_credit RT Σ - MC <= rt_credit RT Σ1 -> cnt_eq ls OW ls1 OW2 -> refs_stable ls OW ls1 OW2 AD ->
        (n <= bn_dmax (getbn r ls1))%nat ->
        (forall q A n0, In (q, A, n0) OW -> bn_d (getbn r ls) <> Some q -> In (q, A, n0) OW2) ->
        rw_cells bsegs m2 (bv_unsigned sp + -112) [CB 8 (take 8 junk0); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        bytes_at bsegs m2 (SRC + Z.of_nat (length zs)) (to_bytes s') ->
        implA (TRet (tt, setbn r (bn_correct_top_pure
                       (mkBN (bn_d (getbn r ls1)) (splice (bn_buf (getbn r ls1)) 0 (bin2bn_limbs s')) n false (bn_flags (getbn r ls1)))) ls1)) Σ1 QQ
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 (SRC + Z.of_nat (length bs) - 1)) x19 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 SHB)
                   (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length s'))) (Z_to_bv 64 (Z.of_nat n - 1)) x28 x29 x30 x31)
              F2 (Z_to_bv 64 0x1efccc) fc2 None m2 (seg_rom bsegs))).
      { intros Σ1 ls1 m2 OW2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 F2 fc2
               HEAP2 LS2 ST2 MI2 AXP2 CR2 CNT2 RST2 HDM BST FR2 HB2.
        clear BNr Ur ARRr LSH MU WM ST MI FR HB' HWLa HWKa DrI SEPrr DrC Dr0 LENr ACC ACCS ACCS1 OFF SHB1 SHB2.
        clear XAI OKq4 BKI.
        pose proof (RST2 _ _ HA) as HA2.
        pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
        destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HA2) as HV2.
        destruct (lib_state_open [] ls1 m2 OW2 AD EA r a LS2 ND2 HA2 ltac:(intros [])) as ((Dr2 & BNr2 & ARRr2) & OKB2 & LSH2).
        pose proof OKB2 as (OKp1 & OKp2 & OKp3 & OKp4).
        destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 r Dr2 HV2 ARRr2) as (Ur2 & LENr2 & Dr20 & DrC2 & DrI2 & DSEPr2).
        pose proof (DSEPr2 r a HA2) as SEPrr2. clear DSEPr2.
        set (br2 := getbn r ls1) in *.
        destruct (ref_at_inb _ _ _ _ _ ADB2 HA2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
        pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
        assert (HDr : exists pr, bn_d br2 = Some pr /\ In (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)) OW2).
        { unfold bn_arr in ARRr2. destruct (bn_d br2) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr2)]|].
          exfalso. destruct ARRr2 as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
        destruct HDr as (pr & Edr & Hinpr).
        pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (PR0 & PR16 & _ & PRC & PRI).
        pose proof (client_block_disj _ _ _ _ _ _ _ _ HEAP2 Hinpr Hbk) as DJL.
        pose proof (client_block_disj _ _ _ _ _ _ _ _ HEAP2 Hinx2 Hbk) as DJS.
        unfold bn_cells in BNr2. unfold BN_WORDS_MAX in OKp3.
        assert (INX2 : In (qx2, Ax2, nx2) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinx2).
        assert (INPR2 : In (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinpr).
        assert (INBK2 : In bk (OW2 ++ LB)) by (apply in_or_app; right; exact Hbk).
        pose proof (AH_acc_in _ _ _ _ (qx2, Ax2, nx2) a 24 HEAP2 INX2 Rx21 Rx22) as ACCa2.
        pose proof (AH_acc_in _ _ _ _ (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)) Dr2 (8 * Z.of_nat (bn_dmax br2)) HEAP2 INPR2 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCD2.
        pose proof (AH_acc_in _ _ _ _ bk (SRC + Z.of_nat (length zs)) (Z.of_nat (length s')) HEAP2 INBK2 ltac:(lia) ltac:(lia)) as ACCS2.
        assert (ALD : Dr2 mod 8 = 0) by (clear - PR16; Z.div_mod_to_equations; lia).
        pose proof (AH_offsh _ _ _ _ (qx2, Ax2, nx2) HEAP2 INX2) as OX2. cbn [blk_addr blk_size fst snd] in OX2. unfold SHLO, SHHI in OX2.
        pose proof (AH_offsh _ _ _ _ (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)) HEAP2 INPR2) as OD2. cbn [blk_addr blk_size fst snd] in OD2. unfold SHLO, SHHI in OD2.
        pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))]%Z m2) as MU2.
        pose proof (wmono_refl bsegs m2) as WM2.
        assert (OFF2 : offshW [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))]).
        { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OX2 OD2 C2 CEIL LO SPR Rx21 Rx22. lia. }
        assert (HWL2 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))]).
        { constructor; [left; cbn; lia|]. constructor; [right; exists (qx2, Ax2, nx2); cbn; auto|].
          constructor; [right; exists (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)); cbn; split; [exact Hinpr| lia]| constructor]. }
        assert (HWK3 : w_okc OW2 LB ls1 AD EA false [r] (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))).
        { eapply (w_limbs OW2 LB ls1 AD EA false [r] _ r pr Dr2); [left; reflexivity| exact HV2| exact Edr| exact Hinpr| cbn [fst snd]; fold br2; lia| cbn [fst snd]; fold br2; lia]. }
        assert (LTB' : length (to_bytes s') = length s') by (unfold to_bytes; apply length_map).
        assert (OFFD : offshW [(Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))]) by (cbn [offshW]; unfold SHLO, SHHI; clear - OD2; lia).
        (* [comment removed for export] *)
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
        assert (A47 : 0 <= a /\ a + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - XB0 XBC Rx21 Rx22 CEIL LO SPT; lia).
        assert (D47 : 0 <= Dr2 /\ Dr2 + 8 * Z.of_nat (bn_dmax br2) <= 140737488355328) by (unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - Dr20 DrC2 CEIL LO SPT; lia).
        clear OX2 OD2 XBI PRI DrI2. apply hide_intro in DJL.
        unfold MallocRep.wz in *.
        apply implA_from_evt.
        step. do 2 step. shl. chk0. step.
        step. do 2 step. shl. chk0. step. step.
        do 4 step. setreg 14%Z (Z_to_bv 64 (shad a)) ltac:(unfold shad; f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
        replace (SRC + Z.of_nat (length bs) - 1) with (SRC + Z.of_nat (length zs) + Z.of_nat (length s') - 1) by lia.
        replace (Z.of_nat n - 1) with (Z.of_nat (n - 1)) by lia.
        assert (LBR2 : length (bn_buf br2) = bn_dmax br2) by reflexivity.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        assert (ACCS3 : acc bsegs m3 (SRC + Z.of_nat (length zs)) (Z.of_nat (length s'))).
        { eapply (acc_munch bsegs _ m2 m3 _ _ ACCS2 MU2 OFF2); unfold BnHeapA.ACEIL in *; lia. }
        assert (ACCD3 : acc bsegs m3 Dr2 (8 * Z.of_nat (bn_dmax br2))).
        { eapply (acc_munch bsegs _ m2 m3 _ _ ACCD2 MU2 OFF2); unfold BnHeapA.ACEIL in *; lia. }
        assert (ACCa3 : acc bsegs m3 a 24) by (eapply (acc_munch bsegs _ m2 m3 _ _ ACCa2 MU2 OFF2); lia).
        eapply (b2b_outerA (n - 1)) with (m0 := m3) (Q := SRC + Z.of_nat (length zs)) (D := Dr2) (A := a) (fl := s') (pre := []) (rest := bn_buf br2);
          [exact HB2 | exact FB' | lia | lia | lia | lia | cbn [app]; exact Ur2 | lia | cbn [app]; lia
          | cbn [app]; apply hide_elim in DJL; clear - DJL BK1 BK2 LBS LBR2; cbn [blk_addr blk_size fst snd] in *; lia
          | exact BNr2 | cbn [app]; clear - SEPrr2 LBR2; lia | lia
          | apply munch_refl | apply wmono_refl | eassumption
          | exact ACCS3 | cbn [app]; rewrite LBR2; exact ACCD3 | exact ALD
          | exact ACCa3 | exact AL | lia | lia
          | lia | cbn [app]; rewrite LBR2; lia | cbn [app]; rewrite LBR2; exact OFFD | ].
        intros t0' t1' t2' a0' a1' a5'' a6' a7' s2' s10' s11' t3' m' UF MUo WMo MIo. cbn [app] in UF, MUo.
        clear HB2 DJS OKp4 ACCS3 ACCD3 ACCS2 ACCa3.
        rewrite LBR2 in MUo.
        transport_after_call bsegs m3 m' MUo WMo. clear MUo WMo.
        set (newbuf := splice (bn_buf br2) 0 (bin2bn_limbs s')).
        apply hide_elim in ENdef.
        destruct (bytes_to_limbs_spec n (rev s')) as [LNL LNN].
        assert (ENB : bytes_to_limbs (S (n - 1)) (rev s') ++ skipn (S (n - 1)) (bn_buf br2) = newbuf).
        { subst newbuf. unfold splice, bin2bn_limbs. rewrite <- ENdef. rewrite firstn_O. cbn [app Nat.add]. rewrite LNN.
          replace (S (n - 1)) with n by lia. reflexivity. }
        rewrite ENB in UF.
        assert (LNB : length newbuf = bn_dmax br2).
        { subst newbuf. rewrite splice_length; [reflexivity|]. unfold bin2bn_limbs. rewrite <- ENdef. rewrite LNN. lia. }
        assert (LMNB : limbs newbuf) by (subst newbuf; apply splice_limbs; [exact OKp1| unfold bin2bn_limbs; rewrite <- ENdef; exact LNL]).
        assert (LWN : Z.of_nat (length (wlimbs newbuf)) = Z.of_nat (bn_dmax br2)) by (rewrite wlimbs_len, LNB; reflexivity).
        apply hide_intro in ENdef.

        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP2 MU2 WM2 HWL2 CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP4.
        assert (ACCD4 : acc bsegs m4 Dr2 (8 * Z.of_nat (length newbuf))).
        { rewrite LNB. eapply (acc_munch bsegs _ m2 m4 _ _ ACCD2 MU2 OFF2); unfold BnHeapA.ACEIL in *; lia. }
        assert (ACCa4 : acc bsegs m4 a 24) by (eapply (acc_munch bsegs _ m2 m4 _ _ ACCa2 MU2 OFF2); lia).
        step. step.
        (* [comment removed for export] *)
        eapply evt_cut.
        { eapply bn_correct_top_specA with (lo := lo) (A := a) (D := Dr2) (b := mkBN (bn_d br2) newbuf n false (bn_flags br2));
            [ unfold bn_cells, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags bn_d Z.b2z]; fold newbuf; rewrite LNB; exact BNr2
            | exact UF | exact LMNB | unfold bn_dmax; cbn [bn_top bn_buf]; fold newbuf; rewrite LNB; exact HDM | unfold bn_dmax; cbn [bn_buf]; fold newbuf; rewrite LNB; lia
            | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MIo
            | rewrite ESP; left; unfold BnHeapA.ACEIL in *; lia | rewrite ESP; left; unfold bn_dmax; cbn [bn_buf]; fold newbuf; rewrite LNB; unfold BnHeapA.ACEIL in *; lia
            | unfold bn_dmax; cbn [bn_buf]; fold newbuf; rewrite LNB; exact SEPrr2
            | exact (AH_shb _ _ _ _ HEAP4) | exact ACCa4 | exact AL | unfold bn_dmax; cbn [bn_buf]; fold newbuf; exact ACCD4 | exact ALD
            | unfold SHHI; lia | clear - OFF2; cbn [offshW] in OFF2; exact (proj1 (proj2 OFF2)) | reflexivity | lia
            | cbn [bn_top]; intros _; split; [lia| exact ALD] ]. }
        intros ms' PO. unfold bn_small_postA in PO.
        destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m5 & E & MUc & WMc & MIc & STc & RES).
        subst ms'. rewrite ESP in *.
        transport_after_call bsegs m4 m5 MUc WMc. clear MUc WMc.
        try rewrite (ret_pc_even 0x1efe00) by lia. step.
        unfold bn_correct_top_pure in RES |- *. cbn [bn_d bn_buf bn_top bn_neg bn_flags] in RES |- *. fold newbuf. fold newbuf in RES.
        replace (if (strip_top newbuf n =? 0)%nat then false else false) with false in RES |- * by (destruct (strip_top newbuf n =? 0)%nat; reflexivity).
        unfold bn_cells, bn_dmax in RES. cbn [bn_d bn_buf bn_top bn_neg bn_flags] in RES. fold newbuf in RES. rewrite LNB in RES.
        assert (STL : (strip_top newbuf n <= n)%nat).
        { clear. generalize n as t. induction t as [|t IHt]; cbn [strip_top]; [lia|]. destruct (nth t newbuf 0 =? 0); lia. }
        (* [comment removed for export] *)
        eapply (FINT Σ1 ls1 m2 OW2 Dr2 m5 newbuf (strip_top newbuf n) false Dr2 (Dr2 + 8 * Z.of_nat (bn_dmax br2)) (bv_unsigned sp - 144));
          [exact HEAP2| exact LSH2| exact HA2| exact AXP2| exact CR2| exact CNT2| exact RST2| exact BST| exact (bn_arr_w_of _ _ _ _ ARRr2)| exact OKB2
          | apply Forall_inv_tail in HWL2; apply Forall_inv_tail in HWL2; apply Forall_inv in HWL2; exact HWL2 | exact HWK3| exact LNB| exact LMNB| lia
          | eassumption | exact RES | exact FR2 | exact STc | exact MIc | lia | exact MU2 | eassumption]. }
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
      assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 144, bv_unsigned sp)]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
      step. if_cases KD; zify_cond KD; rewrite !signed_small in KD by lia.
      * (* [comment removed for export] *)
        apply evt_done. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold br.
        replace (n <=? bn_dmax br)%nat with true by (symmetry; apply Nat.leb_le; lia).
        cbn [tbind fst snd].
        eapply (CONT Σ ls m1 OW);
          [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))
          | exact (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK)
          | exact ST | exact MI
          | exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))
          | exact CR0 | apply cnt_eq_refl | apply refs_stable_refl | fold br; lia
          | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR | exact HB'].
      * (* [comment removed for export] *)
        do 3 step.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
        pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
        pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1'.
        assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
        assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
        { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [CB 8 (take 8 junk0); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                                  (bv_unsigned ra) (bv_unsigned s0) ras);
            [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
          - rewrite !Z_to_bv_bv_unsigned. exact FR.
          - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
        apply evt_done.
        eapply implA_bind.
        { eapply (bn_expand2_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := r) (a := a) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
            [| | | reflexivity | exact HA | reflexivity | reflexivity | lia].
          - unfold bn_preA. rewrite ESP.
            split; [exact HEAP1|]. split; [exact LS1'|]. split; [exact ST|]. split; [exact CEIL|].
            split; [unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
            split; [unfold USTACK_TOP; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact MI|]. split; [exact CNT| exact CRED].
          - rewrite ESP. exact UW1.
          - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_bb_expand (uk_ctx_tail _ _ _ E_bb_tail CTX)). }
        cbv beta. intros [u ls1] Σ1 ms1 PO. unfold bn_postA in PO. cbn [fst snd] in *.
        destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & HEAP2 & LS2 & ST2
                        & MI2 & AXP2 & CR2 & CNT2 & RST2 & -> & HDM & WRES & BST).
        rewrite ESP in *.
        rewrite (ret_pc_even 0x1efcc8) by lia.
        assert (CLI : forall x, SRC <= x < SRC + Z.of_nat (length bs) -> ax_client LB (bv_unsigned sp + -112) LIBW_A x).
        { intros x Hx. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; lia|]. right; right. exists bk. split; [exact Hbk| lia]. }
        assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -112) [CB 8 (take 8 junk0); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_agree; [exact AXP2 | exact FR |].
          intros x Hx. cbn in Hx. split; [|left; unfold USTACK_TOP; lia]. unfold LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
        assert (HB2 : bytes_at bsegs m2 (SRC + Z.of_nat (length zs)) (to_bytes s')).
        { eapply bytes_at_agree; [exact AXP2| exact HB'|]. intros x Hx. apply CLI.
          unfold to_bytes in Hx. rewrite length_map in Hx. lia. }
        apply implA_from_evt.
        step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear KZ.
        apply evt_done. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        eapply (CONT Σ1 ls1 m2 OW2);
          [exact HEAP2 | exact LS2 | exact ST2 | exact MI2
          | eapply ax_pres_trans; [exact AXP1|]; eapply ax_pres_weaken; [exact AXP2| lia]
          | exact CR2 | exact CNT2 | exact RST2 | exact HDM | exact BST | exact FR2 | exact HB2].
Qed.

End WithRT.
