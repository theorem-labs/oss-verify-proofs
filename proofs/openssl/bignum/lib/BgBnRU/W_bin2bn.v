(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnSpecs2 BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnUKit BnUKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnUKit BnUKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Definition byte_ok (c : Z) : Prop := 0 <= c < 256.

(* [comment removed for export] *)
Lemma bytes_head_read : forall m P x (l : list Z) a,
  bytes_at bgusegs m P (to_bytes (x :: l)) -> a = wa P -> ov_read_bytes bgusegs m a 1 = Some [Z_to_bv 8 x].
Proof.
  intros m P x l a HB ->. pose proof (bytes_at_ov_read bgusegs m P _ 0 1 HB ltac:(cbn; lia)) as R.
  replace (P + Z.of_nat 0) with P in R by lia. exact R.
Qed.

Lemma bytes_tail : forall m P x (l : list Z), bytes_at bgusegs m P (to_bytes (x :: l)) -> bytes_at bgusegs m (P + 1) (to_bytes l).
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
Lemma b2b_skip : forall (l : list Z) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
  l <> [] -> Forall byte_ok l -> bytes_at bgusegs m P (to_bytes l) -> Z.of_nat (length l) < 2^31 -> 0 < P -> P + Z.of_nat (length l) < 2^63 ->
  (forall a0' a3' a4' s4', evt bgusegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 1) (Z_to_bv 64 1) a3' a4' a5 a6 a7 s2 s3 s4' (Z_to_bv 64 1) (Z_to_bv 64 0) s7
              s8 (Z_to_bv 64 (Z.of_nat (length (skip_zero_bytes l)))) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xfe6cc) fc None m (seg_rom bgusegs))) ->
  evt bgusegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3
              (Z_to_bv 64 (Z.of_nat (length l))) (Z_to_bv 64 1) (Z_to_bv 64 0) s7
              s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xfe698) fc None m (seg_rom bgusegs)).
Proof.
  induction l as [|x l IH]; intros until P; intros NE FB HB LEN P0 PH K; [congruence|].
  inversion FB as [|? ? Hx FB']; subst. unfold byte_ok in Hx.
  chk ltac:(fun C => clear - C P0 PH; lia).
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in pose proof (bytes_head_read mx P x l a HB ltac:(addr_tac)) as RD end.
  step. clear RD.
  rewrite (zxb_small x) by lia.
  step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by lia.
  - (* [comment removed for export] *)
    rewrite (skip_zero_bytes_nz x l) in K by lia. eapply K.
  - assert (x = 0) by lia. subst x. change (skip_zero_bytes (0 :: l)) with (skip_zero_bytes l) in K.
    step.
    chk ltac:(fun C => clear - C P0 PH; lia).
    step. rewrite (sltu_ge (1 + P) 1) by (clear - P0 PH; lia).
    step.
    chk ltac:(fun C => clear - C; lia).
    step.
    step. rewrite (swrap32_wrap64 (Z.of_nat (length (0 :: l))) (-1)) by (cbn [length] in *; lia).
    step. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    if_cases KL; zify_cond KL; rewrite !signed_small in KL by lia.
    + (* [comment removed for export] *)
      replace (Z.succ (Z.of_nat (length l)) + -1) with (Z.of_nat (length l)) by lia.
      replace (1 + P) with (P + 1) by lia.
      eapply IH; [destruct l; [cbn in KL; lia| discriminate]| exact FB'| eapply bytes_tail; exact HB| lia| lia| lia|].
      intros a0' a3' a4' s4'. eapply K.
    + (* [comment removed for export] *)
      assert (l = []) by (destruct l; [reflexivity| cbn [length] in KL; lia]). subst l. cbn [skip_zero_bytes length] in K.
      step. eapply K.
Qed.

(* [comment removed for export] *)
Lemma b2b_inner : forall (t : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t1 t2 s0 s1 a0 a3 a5 s3 s4 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Q : Z) (fl : list Z) (j : nat) (l : Z),
  bytes_at bgusegs m Q (to_bytes fl) -> Forall byte_ok fl ->
  (1 <= t)%nat -> (j + t <= 8)%nat -> (t <= length fl)%nat -> (t = length fl \/ (j + t = 8)%nat) ->
  0 <= l < 2 ^ (8 * Z.of_nat j) -> Z.of_nat (length fl) < 2^31 -> 1 < Q -> Q + Z.of_nat (length fl) < 2^63 ->
  (forall t0' t1' t2' a5' a6' a7', evt bgusegs POST
     (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 (Z_to_bv 64 2) (Z_to_bv 64 56) a3
              (Z_to_bv 64 (l + 2 ^ (8 * Z.of_nat j) * le_bytes_val (firstn t (rev fl)))) a5' a6' a7'
              (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1 - Z.of_nat t)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl) - Z.of_nat t)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xfe7ac) fc None m (seg_rom bgusegs))) ->
  evt bgusegs POST
     (MS (mkR ra sp gp tp (Z_to_bv 64 (8 * Z.of_nat j)) t1 t2 s0 s1 a0 (Z_to_bv 64 2) (Z_to_bv 64 56) a3
              (Z_to_bv 64 l) a5 (Z_to_bv 64 (Z.of_nat (length fl))) (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1))
              (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl))) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xfe74c) fc None m (seg_rom bgusegs)).
Proof.
  induction t as [|t IH]; intros until l; intros HB FB T1 JT TL TE HL LEN Q0 QH K; [lia|].
  destruct (rev fl) as [|x rfl] eqn:ER; [apply (f_equal (@length Z)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
  assert (EFL : fl = rev rfl ++ [x]) by (rewrite <- (rev_involutive fl), ER; reflexivity).
  assert (LFL : length fl = S (length rfl)) by (rewrite EFL, length_app, length_rev; cbn; lia).
  assert (Hx : byte_ok x) by (rewrite EFL in FB; apply Forall_app in FB; destruct FB as [_ FB]; inversion FB; assumption).
  unfold byte_ok in Hx.
  assert (RD : ov_read_bytes bgusegs m (wa (Q + Z.of_nat (length rfl))) 1 = Some [Z_to_bv 8 x]).
  { rewrite EFL in HB. unfold to_bytes in HB. rewrite map_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite length_map, length_rev in HB. eapply bytes_head_read; [exact HB| reflexivity]. }
  replace (Q + Z.of_nat (length fl) - 1) with (Q + Z.of_nat (length rfl)) by lia.
  chk ltac:(fun C => clear - C Q0 QH LFL; lia).
  step.
  chk ltac:(fun C => clear - C Q0 QH LFL; lia).
  step. rewrite (sltu_lt (-1 + (Q + Z.of_nat (length rfl))) (Q + Z.of_nat (length rfl))) by (clear - Q0 QH LFL; lia).
  step. step.
  chk ltac:(fun C => clear - C; lia).
  step.
  step. clear RD. rewrite (zxb_small x) by lia.
  step. rewrite (swrap32_wrap64 (Z.of_nat (length fl)) (-1)) by lia.
  step. step. step. step. step. step. step.
  rewrite !(unsigned_lit x) by lia. rewrite Z.lxor_0_l.
  replace (Z.land x 255) with x by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z].
  rewrite !(unsigned_lit x) by lia.
  rewrite (unsigned_lit (8 * Z.of_nat j)) by lia. rewrite (Z.mod_small (8 * Z.of_nat j) 64) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (WB : 1 <= 2 ^ (8 * Z.of_nat j) <= 2 ^ 56) by (split; [apply (Z.pow_le_mono_r 2 0); lia| apply Z.pow_le_mono_r; lia]).
  assert (W8 : 2 ^ (8 * Z.of_nat (S j)) = 256 * 2 ^ (8 * Z.of_nat j)).
  { replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  set (W := 2 ^ (8 * Z.of_nat j)) in *.
  rewrite (unsigned_lit (x * W)) by nia. rewrite (unsigned_lit l) by lia.
  rewrite (lor_disjoint (x * W) l (8 * Z.of_nat j)); [| lia | fold W; lia | fold W; apply Z.mod_mul; lia].
  assert (EXIT : t = 0%nat -> forall t0' t1' t2' a5' a6' a7', evt bgusegs POST
     (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 (Z_to_bv 64 2) (Z_to_bv 64 56) a3
              (Z_to_bv 64 (x * W + l)) a5' a6' a7'
              (Z_to_bv 64 (Q + Z.of_nat (length rfl) + -1)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl) + -1)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xfe7ac) fc None m (seg_rom bgusegs))).
  { intros -> t0' t1' t2' a5' a6' a7'. cbn [firstn le_bytes_val] in K. rewrite (Z.mod_small x 256) in K by lia.
    replace (l + W * (x + 256 * 0)) with (x * W + l) in K by lia.
    replace (Q + Z.of_nat (length fl) - 1 - Z.of_nat 1) with (Q + Z.of_nat (length rfl) + -1) in K by lia.
    replace (Z.of_nat (length fl) - Z.of_nat 1) with (Z.of_nat (length fl) + -1) in K by lia.
    eapply K. }
  step. if_cases KR; zify_cond KR; rewrite ?signed_small in KR by lia.
  - (* [comment removed for export] *)
    apply EXIT. lia.
  - step. step. step.
    step. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
    + (* [comment removed for export] *)
      assert (T1' : (1 <= t)%nat) by lia.
      replace (8 * Z.of_nat j + 8) with (8 * Z.of_nat (S j)) by lia.
      replace (-1 + (Q + Z.of_nat (length rfl))) with (Q + Z.of_nat (length (rev rfl)) - 1) by (rewrite length_rev; lia).
      replace (Q + Z.of_nat (length rfl) + -1) with (Q + Z.of_nat (length (rev rfl)) - 1) by (rewrite length_rev; lia).
      replace (Z.of_nat (length fl) + -1) with (Z.of_nat (length (rev rfl))) by (rewrite length_rev; lia).
      eapply (IH POST) with (fl := rev rfl) (j := S j) (l := x * W + l);
        [ rewrite EFL in HB; unfold to_bytes in HB; rewrite map_app in HB; apply bytes_at_app in HB; exact (proj1 HB)
        | rewrite EFL in FB; apply Forall_app in FB; exact (proj1 FB)
        | exact T1' | lia | rewrite length_rev; lia | rewrite length_rev; lia
        | rewrite W8; fold W; nia | rewrite length_rev; lia | exact Q0 | rewrite length_rev; lia | ].
      intros t0' t1' t2' a5' a6' a7'. rewrite rev_involutive, W8. fold W.
      cbn [firstn le_bytes_val] in K. rewrite (Z.mod_small x 256) in K by lia.
      replace (x * W + l + 256 * W * le_bytes_val (firstn t rfl)) with (l + W * (x + 256 * le_bytes_val (firstn t rfl))) by ring.
      replace (Q + Z.of_nat (length (rev rfl)) - 1 - Z.of_nat t) with (Q + Z.of_nat (length fl) - 1 - Z.of_nat (S t)) by (rewrite length_rev; lia).
      replace (Z.of_nat (length (rev rfl)) - Z.of_nat t) with (Z.of_nat (length fl) - Z.of_nat (S t)) by (rewrite length_rev; lia).
      eapply K.
    + step. apply EXIT. lia.
Qed.

Lemma upd_app_mid' : forall {X} (l1 : list X) x l2 v, Arr.upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|y l1 IH]; intros x l2 v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma b2b_outer : forall (k : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (Q D A : Z) (fl pre rest : list Z),
  bytes_at bgusegs m Q (to_bytes fl) -> Forall byte_ok fl ->
  8 * Z.of_nat k < Z.of_nat (length fl) <= 8 * Z.of_nat k + 8 -> Z.of_nat (length fl) < 2^31 -> 1 < Q -> Q + Z.of_nat (length fl) < 2^63 ->
  u64arr bgusegs m D (wlimbs (pre ++ rest)) -> (S k <= length rest)%nat -> Z.of_nat (length (pre ++ rest)) < 2^31 ->
  (D + 8 * Z.of_nat (length (pre ++ rest)) <= Q \/ Q + Z.of_nat (length fl) <= D) ->
  rw_cells bgusegs m A [C8 (Z_to_bv 64 D)] -> (A + 8 <= D \/ D + 8 * Z.of_nat (length (pre ++ rest)) <= A) -> 0 < D -> D mod 8 = 0 ->
  munch [(D, D + 8 * Z.of_nat (length (pre ++ rest)))] m0 m -> wmono bgusegs m0 m -> mem_inv bgusegs m ->
  (forall a0' a3' a4' a5' a6' a7' t0' t1' t2' s2' s9' s10' m',
     u64arr bgusegs m' D (wlimbs (pre ++ bytes_to_limbs (S k) (rev fl) ++ skipn (S k) rest)) ->
     munch [(D, D + 8 * Z.of_nat (length (pre ++ rest)))] m0 m' -> wmono bgusegs m0 m' -> mem_inv bgusegs m' ->
     evt bgusegs POST
       (MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' (Z_to_bv 64 2) (Z_to_bv 64 56) a3' a4' a5' a6' a7'
                s2' s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s9' s10' s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xfe7e8) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs POST
     (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length pre))) (Z_to_bv 64 2) (Z_to_bv 64 56) a3 a4 a5 a6 a7
              (Z_to_bv 64 (Q + Z.of_nat (length fl) - 1)) s3 s4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
              (Z_to_bv 64 (Z.of_nat (length fl))) (Z_to_bv 64 (Z.of_nat k)) s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0xfe734) fc None m (seg_rom bgusegs)).
Proof.
  induction k as [|k IH]; intros until rest; intros HB FB KL LEN Q0 QH U KR LPR DJ RDD DJA D0 D8 MU WM MI K.
  all: pose proof (u64arr_bound bgusegs m D _ U) as UB; rewrite wlimbs_len in UB.
  all: step; step; (if_cases KZ; zify_cond KZ; [exfalso; apply andb_false_iff in KZ; destruct KZ as [KZ|KZ]; apply Z.ltb_ge in KZ; lia|]); clear KZ0 KZ1.
  all: step; step; step; step.
  - (* [comment removed for export] *)
    eapply (b2b_inner (length fl) POST) with (fl := fl) (j := 0%nat) (l := 0);
      [exact HB| exact FB| lia| lia| lia| left; reflexivity| cbn; lia| exact LEN| exact Q0| exact QH|].
    intros t0' t1' t2' a5' a6' a7'. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.mul_1_l, Z.add_0_l.
    rewrite <- (length_rev fl) at 1. rewrite firstn_all.
    step. step. step.
    rewrite (unsigned_lit (Z.of_nat (length pre))) by (rewrite length_app in LPR; lia). rewrite Z.shiftl_mul_pow2 by lia.
    replace (D + Z.of_nat (length pre) * 2 ^ 3) with (D + 8 * Z.of_nat (length pre)) by lia.
    destruct rest as [|r0 rest']; [cbn in KR; lia|].
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ r0 :: rest')))) by (rewrite wlimbs_len, length_app; cbn [length]; lia).
    assert (IDX' : Z.of_nat (length pre) < Z.of_nat (length (pre ++ r0 :: rest'))) by (rewrite length_app; cbn [length]; lia).
    chk ltac:(fun C => clear - C D0 UB IDX'; lia).
    step. rewrite (snez_pos D) by (clear - D0 UB IDX'; lia).
    step. rewrite (seqz_pos (D + 8 * Z.of_nat (length pre))) by (clear - D0 UB IDX'; lia).
    step.
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => clear - C D0 UB IDX'; lia).
    step. rewrite (land7_wrap (D + 8 * Z.of_nat (length pre))) by (clear - D8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    pose proof (u64arr_store_ok bgusegs m D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW.
    pose proof (u64arr_write bgusegs m D _ (Z.of_nat (length pre)) (Z_to_bv 64 (le_bytes_val (rev fl))) U IDX) as U2.
    step. store_done.
    step. step.
    step. if_false.
    eapply K; [| exact MU| exact WM| exact MI].
    rewrite Nat2Z.id in U2. unfold wlimbs in U2. rewrite map_app in U2. cbn [map] in U2.
    rewrite <- (length_map (fun x : Z => Z_to_bv 64 x) pre) in U2. rewrite upd_app_mid' in U2.
    cbn [bytes_to_limbs skipn app]. unfold wlimbs. rewrite map_app. cbn [map].
    rewrite firstn_all2 by (rewrite length_rev; lia). exact U2.
  - (* [comment removed for export] *)
    eapply (b2b_inner 8 POST) with (fl := fl) (j := 0%nat) (l := 0);
      [exact HB| exact FB| lia| lia| lia| right; reflexivity| cbn; lia| exact LEN| exact Q0| exact QH|].
    intros t0' t1' t2' a5' a6' a7'. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.mul_1_l, Z.add_0_l.
    step. step. step.
    rewrite (unsigned_lit (Z.of_nat (length pre))) by (rewrite length_app in LPR; lia). rewrite Z.shiftl_mul_pow2 by lia.
    replace (D + Z.of_nat (length pre) * 2 ^ 3) with (D + 8 * Z.of_nat (length pre)) by lia.
    destruct rest as [|r0 rest']; [cbn in KR; lia|].
    set (v := le_bytes_val (firstn 8 (rev fl))) in *.
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ r0 :: rest')))) by (rewrite wlimbs_len, length_app; cbn [length]; lia).
    assert (IDX' : Z.of_nat (length pre) < Z.of_nat (length (pre ++ r0 :: rest'))) by (rewrite length_app; cbn [length]; lia).
    assert (LTB : length (to_bytes fl) = length fl) by (unfold to_bytes; apply length_map).
    assert (LPR' : Z.of_nat (length (pre ++ r0 :: rest')) = Z.of_nat (length pre) + 1 + Z.of_nat (length rest')) by (rewrite length_app; cbn [length]; lia).
    chk ltac:(fun C => clear - C D0 UB IDX'; lia).
    step. rewrite (snez_pos D) by (clear - D0 UB IDX'; lia).
    step. rewrite (seqz_pos (D + 8 * Z.of_nat (length pre))) by (clear - D0 UB IDX'; lia).
    step.
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => clear - C D0 UB IDX'; lia).
    step. rewrite (land7_wrap (D + 8 * Z.of_nat (length pre))) by (clear - D8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    pose proof (u64arr_store_ok bgusegs m D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW.
    pose proof (u64arr_write bgusegs m D _ (Z.of_nat (length pre)) (Z_to_bv 64 v) U IDX) as U2.
    step. store_done.
    step.
    step. rewrite (swrap32_wrap64 (Z.of_nat (S k)) (-1)) by lia.
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
      | lia | lia | exact Q0 | lia
      | | cbn [length] in KR; lia | rewrite ELEN; exact LPR | rewrite ELEN; lia
      | exact RDD | rewrite ELEN; exact DJA | exact D0 | exact D8
      | rewrite ELEN; exact MU | exact WM | exact MI | ].
    + rewrite Nat2Z.id in U2. unfold wlimbs in U2. rewrite map_app in U2. cbn [map] in U2.
      rewrite <- (length_map (fun x : Z => Z_to_bv 64 x) pre) in U2. rewrite upd_app_mid' in U2.
      unfold wlimbs. rewrite <- app_assoc, map_app. cbn [map app]. exact U2.
    + intros a0' a3' a4' a5'' a6'' a7'' t0'' t1'' t2'' s2' s9' s10' m' UF MUF WMF MIF.
      eapply K; [| rewrite ELEN in MUF; exact MUF| exact WMF| exact MIF].
      cbn [bytes_to_limbs skipn]. fold v. rewrite skipn_rev. fold fl'.
      rewrite <- app_assoc in UF. cbn [app] in UF. exact UF.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_BIN2BN : Z := 0xfe568.
Definition BN_BIN2BN_STACK : Z := 96 + BN_EXPAND2_STACK.

(* [comment removed for export] *)
Lemma client_block_disj : forall s (OW LB : list block) m q A n bk,
  RHEAP s (OW ++ LB) m -> In (q, A, n) OW -> In bk LB -> A + n <= blk_addr bk \/ blk_addr bk + blk_size bk <= A.
Proof.
  intros s OW LB m q A n bk HEAP Hq Hb. pose proof (LH_nodup _ _ _ HEAP) as ND.
  assert (NE : blk_id (q, A, n) <> blk_id bk).
  { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id (q, A, n)) ND); [apply in_map; exact Hq| rewrite E; apply in_map; exact Hb]. }
  pose proof (LH_disjoint _ _ _ (q, A, n) bk HEAP ltac:(apply in_or_app; left; exact Hq) ltac:(apply in_or_app; right; exact Hb) NE) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. cbn [blk_addr blk_size fst snd]. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_bin2bn_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a : Z) (SRC : Z) (xs : list Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_BIN2BN_STACK -> tp = wz RATP ->
    ref_at bs OW PL r a -> wref PL r ->
    bytes_at bgusegs m SRC (to_bytes xs) -> Forall byte_ok xs -> Z.of_nat (length xs) < 2^31 -> 0 < SRC -> SRC + Z.of_nat (length xs) < 2^63 ->
    (xs = [] \/ exists bk, In bk LB /\ blk_addr bk <= SRC /\ SRC + Z.of_nat (length xs) <= blk_addr bk + blk_size bk) ->
    a0 = wz SRC -> a1 = wz (Z.of_nat (length xs)) -> a2 = wz a ->
    implM bgusegs (interp (embed (BN_bin2bn (tree_ops bptr) xs r bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz a /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_BIN2BN) fc None m (seg_rom bgusegs)).
  Proof.
    intros until xs. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HA WR HB FB LEN SRC0 SRCH HBK -> -> ->. pose proof (proj1 WR) as NRO.
    unfold BN_BIN2BN_STACK, BN_EXPAND2_STACK, BN_BIN2BN, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (XA0 & XAC & XAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO) as (PA0 & PA8).
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    apply hide_intro in HB. rename HB into HBH.
    unfold implM. iprefix.

    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp). step.

    (* [comment removed for export] *)
    carve_frame 96%nat ST. do 14 step.
    step. if_cases KN; zify_cond KN; [exfalso; lia|]. clear KN.
    do 5 step. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step.

    assert (FINT : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word) (Dr : Z)
                          (mF : mem) (nb : list Z) (top' : nat) (neg' : bool) (l3 h3 : Z) (jk : list byte)
                          (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state_h [r] bs1 m2 OW2 PL EA -> ref_at bs1 OW2 PL r a -> rauxv_ok m2 B ->
      lx_pres LB (bv_unsigned sp) (XW PL) m m2 -> ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n) OW2) ->
      bn_arr m2 OW2 (pl_of PL r) Dr (getbn r bs1) -> bg_ok (getbn r bs1) ->
      w_lib bs1 OW2 PL lo (bv_unsigned sp) (l3, h3) -> w_okc OW2 LB bs1 PL EA (bv_unsigned sp) false [r] (l3, h3) ->
      length nb = bn_dmax (getbn r bs1) -> limbs nb -> (top' <= length nb)%nat ->
      u64arr bgusegs mF Dr (wlimbs nb) ->
      rw_cells bgusegs mF a [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat top')); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax (getbn r bs1))));
                           C4 (Z_to_bv 64 (Z.b2z neg')); C4 (Z_to_bv 64 (bn_flags (getbn r bs1)))] ->
      rw_cells bgusegs mF (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells bgusegs mF 3346164 [C4 errv2] -> stk bgusegs mF lo (bv_unsigned sp + -96) -> mem_inv bgusegs mF ->
      munch [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (l3, h3)]%Z m2 mF -> wmono bgusegs m2 mF ->
      evt bgusegs
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
           (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 a /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n) OW'))
           (tt, setbn r (mkBN (bn_d (getbn r bs1)) nb top' neg' (bn_flags (getbn r bs1))) bs1) st1)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xfe810) fc None mF (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 Dr mF nb top' neg' l3 h3 jk x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
             HEAP2 LSH HA2 AUX2 LXP2 FA2 SO2 RST2 BST ARR2 OKB HW3L HW3K Lnb LMnb TOPB UF BNF FRF ERRF STF MIF MUF WMF.
      clear MU WM MI ERR ST FR.
      pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSH) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSH HA2) as HV2.
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK HA2 NRO) as (XB0 & XBC & XBI).
      set (br := getbn r bs1) in *.
      step. do 12 step. step. release_frame FRF STF (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (l3, h3)]).
      { constructor; [left; cbn; lia|]. constructor; [right; right; exists r, a; split; [exact HA2|]; split; [exact NRO|]; cbn; lia|]. constructor; [exact HW3L| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) [r]) [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (l3, h3)]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB bs1 PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HA2| assumption| cbn; lia| cbn; lia]|].
        constructor; [exact HW3K| constructor]. }
      destruct OKB as (OKq1 & OKq2 & OKq3 & OKq4).
      unfold bn_post. do 15 eexists. exists mG, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MUF WMF HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs1 mG OW2 PL EA r a); [| exact ND2| exact HA2| exact NRO| | |].
        - exact (lib_state_frame st1 LB _ _ [r] bs1 m2 mG OW2 PL EA _ HEAP2 LSH MUF WMF FROK WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNF.
          + pose proof ARR2 as ARR2'. unfold bn_arr in ARR2'. destruct (bn_d br) as [pr|] eqn:Edb.
            * unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. unfold bn_dmax in Lnb. rewrite Lnb. split; [exact (proj1 ARR2')| exact UF].
            * destruct (bn_arr_null PL r m2 OW2 Dr br PWF2 WR Edb ARR2) as [ED Eb].
              unfold bn_dmax in Lnb. rewrite Eb in Lnb. cbn in Lnb.
              apply (bn_arr_nil_intro PL r mG OW2 Dr _ PWF2 WR ED); [destruct nb; [reflexivity| cbn in Lnb; discriminate Lnb]| reflexivity].
        - unfold bg_ok, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
          split; [exact LMnb|]. split; [lia|]. split; [exact OKq3| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HV2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK AUX2 MUF WMF HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact STF|].
      split; [unfold LX_ERRNO, RATP; exact ERRF|]. split; [exact MIF|].
      split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MUF WMF HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
      split; [reflexivity|]. split; [reflexivity| exact BST]. }

    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((Dr & BNr & ARRr) & OKB & LSH).
    pose proof OKB as (OKq1 & OKq2 & OKq3 & OKq4).
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK r Dr HV NRO ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    pose proof (DSEPr r a HA) as SEPrr. clear DSEPr.
    set (br := getbn r bs) in *.
    unfold bn_cells in BNr. unfold BG_DMAX in OKq3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of MU with munch ?W0 _ _ =>
      apply (rw_cells_transport bgusegs W0 m m1 a) in BNr; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (u64arr_transport bgusegs W0 m m1 Dr) in Ur; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LENr; lia] end.
    unfold BN_bin2bn, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. fold br.
    assert (HWLa : w_lib bs OW PL lo (bv_unsigned sp) (a, a + 24)) by (right; right; exists r, a; split; [exact HA|]; split; [exact NRO|]; cbn; lia).
    assert (HWKa : w_okc OW LB bs PL EA (bv_unsigned sp) false [r] (a, a + 24)) by (eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [r] _ r a); [left; reflexivity| exact HA| assumption| cbn; lia| cbn; lia]).
    assert (LXP0 : lx_pres LB (bv_unsigned sp) (XW PL) m m) by apply lx_pres_refl.
    step. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by lia.
    - (* [comment removed for export] *)
      assert (xs = []) by (destruct xs; [reflexivity| cbn [length] in KL; lia]). subst xs.
      (* [comment removed for export] *)
      step. step.
      remember (Z_to_bv 64 1041984) as ra1 eqn:Era1.
      assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
      carve_frame 32%nat ST. do 5 step.
      step. if_cases KNZ; zify_cond KNZ; [exfalso; rewrite ?unsigned_lit in KNZ by lia; lia|]. clear KNZ.
      step. step. rewrite (land7_wrap _ PA8).
      chk ltac:(fun C => clear - C; lia).
      step. unfold MallocRep.wz at 1.
      step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
      + (* [comment removed for export] *)
        assert (EB : bn_buf br = []).
        { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pd|] eqn:Edb; [|exact (proj2 (bn_arr_null PL r m OW Dr br PWF WR Edb ARRr))].
          exfalso. pose proof (RH_range _ _ _ _ _ _ _ HEAP (proj1 ARRr')) as (P0 & _). lia. }
        assert (ED0 : bn_dmax br = 0%nat) by (unfold bn_dmax; rewrite EB; reflexivity).
        apply (munch_weaken _ [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]%Z) in MU; [| intros x Hx; cbn [outside] in *; split; [exact (proj1 Hx)| exact I]].
        ihere. to_implM. cbn [embed interp]. apply implM_ret.
        unfold MallocRep.wz in *.
        step. step.
        do 3 step. step. release_frame FR0 ST (bv_unsigned sp + -96). subst ra1. step.
        rewrite ?ret_pc_even by first [lia | reflexivity].
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (FINT s bs m OW errv Dr mx (repeat 0 (bn_dmax br)) 0%nat false a (a + 24) []);
            [exact HEAP| exact LSH| exact HA| exact AUX| exact LXP0| reflexivity| reflexivity| apply refs_stable_refl
            | intros q0 A0 n0 Hq0 _; exact Hq0| exact ARRr| exact OKB| exact HWLa| exact HWKa
            | apply repeat_length| rewrite ED0; constructor| lia
            | rewrite ED0; cbn [repeat]; rewrite EB in Ur; exact Ur | exact BNr| exact FR| exact ERR| exact ST| exact MI| exact MU| exact WM] end.
      + (* [comment removed for export] *)
        assert (HDr : exists pd, bn_d br = Some pd /\ In (pd, Dr, 8 * Z.of_nat (bn_dmax br)) OW).
        { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pd|] eqn:Edb; [exists pd; split; [reflexivity| exact (proj1 ARRr')]|].
          exfalso. destruct (bn_arr_null PL r m OW Dr br PWF WR Edb ARRr) as [ED _]. lia. }
        destruct HDr as (pd & Edr & Hinpd).
        pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinpd) as (PD0 & _ & _ & PDC & PDI).
        assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 144, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
        apply limbarr_CB in Ur. fold (bn_dmax br) in Ur.
        ihere. to_implM. cbn [embed interp]. apply implM_ret.
        unfold MallocRep.wz in *.
        step. rewrite (sx32_small (Z.of_nat (bn_dmax br))) by lia.
        step. rewrite (unsigned_lit (Z.of_nat (bn_dmax br))) by lia.
        replace (Z.shiftl (Z.of_nat (bn_dmax br)) 3) with (8 * Z.of_nat (bn_dmax br)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (lib_state_frame s LB _ _ [] bs m mx OW PL EA _ HEAP LS MU WM FROK WOK) as LS1;
          apply (munch_weaken _ [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z) in MU;
            [| intros x Hx; cbn [outside] in *; split; [exact (proj1 Hx)| exact I]];
          eapply evt_cut;
          [ eapply (OPENSSL_cleanse_spec) with (D := Dr) (N := 8 * Z.of_nat (bn_dmax br)) (junk := u64s (wlimbs (bn_buf br))) (lo := lo);
              rewrite ?ESP2; [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact (proj1 LS1)
              | replace (Z.to_nat (8 * Z.of_nat (bn_dmax br))) with (8 * bn_dmax br)%nat by lia; exact Ur
              | lia| lia| unfold GLOBALS_TOP; lia| reflexivity| reflexivity]
          | rewrite ?ESP2; post_call bgusegs mx ] end.
        step. step.
        do 3 step. step. release_frame FR0 PC (bv_unsigned sp + -96). subst ra1. step.
        rewrite ?ret_pc_even by first [lia | reflexivity].
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (FINT s bs m OW errv Dr mx (repeat 0 (bn_dmax br)) 0%nat false Dr (Dr + 8 * Z.of_nat (bn_dmax br)) []);
            [exact HEAP| exact LSH| exact HA| exact AUX| exact LXP0| reflexivity| reflexivity| apply refs_stable_refl
            | intros q0 A0 n0 Hq0 _; exact Hq0| exact ARRr| exact OKB
            | right; left; exists (pd, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpd| lia]
            | eapply (w_limbs OW LB bs PL EA (bv_unsigned sp) false [r] _ r pd Dr); [left; reflexivity| exact HV| exact Edr| exact Hinpd| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]
            | apply repeat_length| apply limbs_repeat; exact limb_0| lia
            | | exact BNr| exact FR| exact ERR| exact PC| eassumption| exact MU| exact WM] end.
        eapply (CB_u64arr bgusegs _ Dr). rewrite lbytes_repeat0.
        replace (8 * bn_dmax br)%nat with (Z.to_nat (8 * Z.of_nat (bn_dmax br))) by lia. eassumption.
    - (* [comment removed for export] *)
      destruct xs as [|x0 xs'] eqn:EBS; [cbn [length] in KL; lia|]. cbv iota. rewrite <- EBS in *.
      assert (NEB : xs <> []) by (rewrite EBS; discriminate).
      destruct HBK as [HBK|(bk & Hbk & BK1 & BK2)]; [congruence|].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hbk)) as (BK0 & BK16 & _ & BKC & BKI).
      assert (SRC16 : 16 <= SRC) by (clear - BK0 BK16 BK1; Z.div_mod_to_equations; lia). clear BK0 BK16.
      set (s' := skip_zero_bytes xs) in *.
      assert (LTB : length (to_bytes xs) = length xs) by (unfold to_bytes; apply length_map).
      pose proof (hide_elim _ HBH) as HB1.
      lazymatch type of MU with munch ?W0 _ _ =>
        apply (bytes_at_transport bgusegs W0 m m1 SRC) in HB1; [| exact MU| cbn [disjoint_from]; rewrite LTB; lia] end.
      step. if_true.
      step. rewrite (swrap32_wrap64 (Z.of_nat (length xs)) (-1)) by lia.
      step.
      chk ltac:(fun C => clear - C SRC0 SRCH LEN KL; lia).
      step. rewrite (snez_pos SRC) by (clear - SRC0 SRCH; lia).
      step. rewrite (seqz_pos (Z.of_nat (length xs) + -1 + SRC)) by (clear - SRC0 SRCH KL; lia).
      step.
      chk ltac:(fun C => clear - C; lia).
      step. step. step. step.
      step. if_true.
      step. step. step.
      step. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1. change (Z.b2z (0 <? 1)) with 1.
      step. step.
      eapply (b2b_skip xs); [exact NEB| exact FB| exact HB1| exact LEN| exact SRC0| exact SRCH|].
      intros a0' a3' a4' s4'. fold s'.
      step. step. if_true.
      destruct (skip_zero_bytes_suffix xs) as (zs & ESFX). fold s' in ESFX.
      assert (FB' : Forall byte_ok s') by (rewrite ESFX in FB; apply Forall_app in FB; exact (proj2 FB)).
      assert (LBS : length xs = (length zs + length s')%nat) by (rewrite ESFX at 1; apply length_app).
      assert (HB' : bytes_at bgusegs m1 (SRC + Z.of_nat (length zs)) (to_bytes s')).
      { rewrite ESFX in HB1. unfold to_bytes in HB1. rewrite map_app in HB1. apply bytes_at_app in HB1. rewrite length_map in HB1. exact (proj2 HB1). }
      clearbody s'. clear HB1.
      step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
      + (* [comment removed for export] *)
        assert (s' = []) by (destruct s'; [reflexivity| cbn [length] in KS; lia]). subst s'.
        apply (munch_weaken _ [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (a, a + 24)]%Z) in MU; [| intros x Hx; cbn [outside] in *; split; [exact (proj1 Hx)| exact I]].
        ihere. to_implM. cbn [embed interp]. apply implM_ret.
        unfold MallocRep.wz in *.
        step. rewrite (land7_wrap _ PA8).
        chk ltac:(fun C => clear - C; lia).
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (FINT s bs m OW errv Dr mx (bn_buf br) 0%nat (bn_neg br) a (a + 24) []);
            [exact HEAP| exact LSH| exact HA| exact AUX| exact LXP0| reflexivity| reflexivity| apply refs_stable_refl
            | intros q0 A0 n0 Hq0 _; exact Hq0| exact ARRr| exact OKB| exact HWLa| exact HWKa
            | reflexivity| exact OKq1| lia
            | exact Ur | exact BNr| exact FR| exact ERR| exact ST| exact MI| exact MU| exact WM] end.
      + (* [comment removed for export] *)
        assert (LS1 : (1 <= length s')%nat) by lia.
        destruct s' as [|yb0 sb''] eqn:ES'; [cbn [length] in LS1; lia|]. cbv iota beta. rewrite <- ES' in *. fold br.
        step. rewrite (swrap32_wrap64 (Z.of_nat (length s')) (-1)) by lia.
        zstep. if_cases C; [exfalso; zify_cond C; rewrite ?signed_small in C by lia; clear - C; lia| clear C].
        step. rewrite (land7_wrap _ PA8).
        chk ltac:(fun C => clear - C; lia).
        step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax br))) by lia.
        step. step.
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
        rewrite !ES10. replace (Z.of_nat n - 1 + 1) with (Z.of_nat n) by lia.

        assert (CONT : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                              (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
          RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -96) ->
          rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
          ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
          (n <= bn_dmax (getbn r bs1))%nat ->
          (forall q A n0, In (q, A, n0) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n0) OW2) ->
          rw_cells bgusegs m2 (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
          bytes_at bgusegs m2 (SRC + Z.of_nat (length zs)) (to_bytes s') ->
          implM bgusegs (interp (embed (TRet (tt, setbn r (bn_correct_top_pure
                         (mkBN (bn_d (getbn r bs1)) (splice (bn_buf (getbn r bs1)) 0 (bin2bn_limbs s')) n false (bn_flags (getbn r bs1)))) bs1)))) st1
            (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                     (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 a /\ (forall q A n0, In (q, A, n0) OW -> bn_d (getbn r bs) <> Some q -> In (q, A, n0) OW')))
            (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 (Z.of_nat (length xs) + -1 + SRC)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1)
                     (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length s')))
                     (Z_to_bv 64 (Z.of_nat n - 1)) s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0xfe720) fc None m2 (seg_rom bgusegs))).
        { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
                 HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 HDM BST FR2 HB2.
          clear BNr Ur ARRr LSH MU WM ST ERR MI FR HB' HWLa HWKa DrI SEPrr DrC Dr0 LENr.
          clear XAI OKq4 BKI.
          pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HA) as HA2.
          pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
          pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HA2) as HV2.
          destruct (lib_state_open [] bs1 m2 OW2 PL EA r a LS2 ND2 HA2 ltac:(intros []) NRO) as ((Dr2 & BNr2 & ARRr2) & OKB2 & LSH2).
          pose proof OKB2 as (OKp1 & OKp2 & OKp3 & OKp4).
          destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK r Dr2 HV2 NRO ARRr2) as (Ur2 & LENr2 & Dr20 & DrC2 & DrI2 & DSEPr2).
          pose proof (DSEPr2 r a HA2) as SEPrr2. clear DSEPr2.
          set (br2 := getbn r bs1) in *.
          pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK HA2 NRO) as (XB0 & XBC & XBI).
          assert (HDr : exists pr, bn_d br2 = Some pr /\ In (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)) OW2).
          { pose proof ARRr2 as ARRr2'. unfold bn_arr in ARRr2'. destruct (bn_d br2) as [pr|] eqn:Edb; [exists pr; split; [reflexivity| exact (proj1 ARRr2')]|].
            exfalso. destruct (bn_arr_null PL r m2 OW2 Dr2 br2 PWF2 WR Edb ARRr2) as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
          destruct HDr as (pr & Edr & Hinpr).
          pose proof (client_block_disj _ _ _ _ _ _ _ _ HEAP2 Hinpr Hbk) as DJL.
          pose proof (struct_client_disj _ _ _ _ _ _ _ _ _ r a bk HEAP2 PARTS2 FROK HA2 NRO Hbk) as DJS.
          unfold bn_cells in BNr2. unfold BG_DMAX in OKp3.
          cbn [embed interp]. apply implM_ret.
          pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (a, a + 24); (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))]%Z m2) as MU2.
          pose proof (wmono_refl bgusegs m2) as WM2.
          assert (LTB' : length (to_bytes s') = length s') by (unfold to_bytes; apply length_map).
          unfold MallocRep.wz in *.
          pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (DR0 & DR16 & _).
          assert (DR8 : Dr2 mod 8 = 0) by (clear - DR16; Z.div_mod_to_equations; lia).
          destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 HA2 NRO) as (PB0 & PB8).
          step. step. step. step. step.
          replace (Z.of_nat (length xs) + -1 + SRC) with (SRC + Z.of_nat (length zs) + Z.of_nat (length s') - 1) by lia.
          replace (Z.of_nat n - 1) with (Z.of_nat (n - 1)) by lia.
          assert (LBR2 : length (bn_buf br2) = bn_dmax br2) by reflexivity.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          assert (RDD : rw_cells bgusegs m3 a [C8 (Z_to_bv 64 Dr2)]).
          { lazymatch type of BNr2 with rw_cells _ _ _ (?c :: ?cs) => exact (proj1 (proj1 (bk_rw_cells_app bgusegs m3 a [c] cs) BNr2)) end. }
          eapply (b2b_outer (n - 1)) with (m0 := m3) (Q := SRC + Z.of_nat (length zs)) (D := Dr2) (A := a) (fl := s') (pre := []) (rest := bn_buf br2);
            [exact HB2 | exact FB' | lia | lia | lia | lia | cbn [app]; exact Ur2 | lia | cbn [app]; lia
            | cbn [app]; clear - DJL BK1 BK2 LBS LBR2; cbn [blk_addr blk_size fst snd] in *; lia
            | exact RDD | cbn [app]; clear - SEPrr2 LBR2; lia | exact DR0 | exact DR8
            | apply munch_refl | apply wmono_refl | eassumption | ].
          intros c0' c3' c4' c5' c6' c7' u0' u1' u2' v2' v9' v10' m' UF MUo WMo MIo. cbn [app] in UF, MUo.
          clear HB2 DJL DJS OKp4 RDD.
          rewrite LBR2 in MUo.
          transport_after_call bgusegs m3 m' MUo WMo. clear MUo WMo. clear DrI2.
          set (newbuf := splice (bn_buf br2) 0 (bin2bn_limbs s')).
          destruct (bytes_to_limbs_spec n (rev s')) as [LNL LNN].
          assert (ENB : bytes_to_limbs (S (n - 1)) (rev s') ++ skipn (S (n - 1)) (bn_buf br2) = newbuf).
          { subst newbuf. unfold splice, bin2bn_limbs. fold n. rewrite firstn_O. cbn [app Nat.add]. rewrite LNN.
            replace (S (n - 1)) with n by lia. reflexivity. }
          rewrite ENB in UF.
          assert (LNB : length newbuf = bn_dmax br2).
          { subst newbuf. rewrite splice_length; [reflexivity|]. unfold bin2bn_limbs. fold n. rewrite LNN. lia. }
          assert (LMNB : limbs newbuf) by (subst newbuf; apply splice_limbs; [exact OKp1| unfold bin2bn_limbs; fold n; exact LNL]).
          assert (LWN : Z.of_nat (length (wlimbs newbuf)) = Z.of_nat (bn_dmax br2)) by (rewrite wlimbs_len, LNB; reflexivity).
          assert (HWL3 : w_lib bs1 OW2 PL lo (bv_unsigned sp) (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))).
          { right; left. exists (pr, Dr2, 8 * Z.of_nat (bn_dmax br2)). cbn. split; [exact Hinpr| lia]. }
          assert (HWK3 : w_okc OW2 LB bs1 PL EA (bv_unsigned sp) false [r] (Dr2, Dr2 + 8 * Z.of_nat (bn_dmax br2))).
          { eapply (w_limbs OW2 LB bs1 PL EA (bv_unsigned sp) false [r] _ r pr Dr2); [left; reflexivity| exact HV2| exact Edr| exact Hinpr| cbn [fst snd]; fold br2; lia| cbn [fst snd]; fold br2; lia]. }
          unfold bn_correct_top_pure. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. fold newbuf.
          replace (if (strip_top newbuf n =? 0)%nat then false else false) with false by (destruct (strip_top newbuf n =? 0)%nat; reflexivity).
          assert (STL : (strip_top newbuf n <= n)%nat).
          { clear. generalize n as t. induction t as [|t IHt]; cbn [strip_top]; [lia|]. destruct (nth t newbuf 0 =? 0); lia. }
          (* [comment removed for export] *)
          assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
          step. step.
          set (bF := mkBN (bn_d br2) newbuf n false (bn_flags br2)).
          assert (BNF : rw_cells bgusegs m' a (bn_cells Dr2 bF)).
          { unfold bn_cells, bF, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite LNB. exact BNr2. }
          eapply evt_cut.
          { eapply (bn_correct_top_spec) with (lo := lo) (A := a) (D := Dr2) (b := bF); rewrite ?ESP;
              [ exact BNF | split; [exact PB0| exact PB8] | intros _; split; [exact DR0| exact DR8]
              | exact UF | exact LMNB | unfold bF, bn_dmax; cbn [bn_top bn_buf]; rewrite LNB; exact HDM
              | unfold bF, bn_dmax; cbn [bn_buf]; rewrite LNB; lia
              | exact ST2 | lia | eassumption | lia
              | unfold bF, bn_dmax; cbn [bn_buf]; rewrite LNB; lia
              | unfold bF, bn_dmax; cbn [bn_buf]; rewrite LNB; lia
              | reflexivity ]. }
          rewrite ?ESP. post_call bgusegs m'.
          rewrite ESP in PC.
          unfold BnRep.bn_cells, bn_cells, bn_correct_top_pure, bF, bn_dmax, MallocRep.wz in POST. cbn [bn_d bn_buf bn_top bn_neg bn_flags] in POST. rewrite ?LNB in POST.
          replace (if (strip_top newbuf n =? 0)%nat then false else false) with false in POST by (destruct (strip_top newbuf n =? 0)%nat; reflexivity).
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply (FINT st1 bs1 m2 OW2 errv2 Dr2 mx newbuf (strip_top newbuf n) false Dr2 (Dr2 + 8 * Z.of_nat (bn_dmax br2)) []);
              [exact HEAP2| exact LSH2| exact HA2| exact AUX2| exact LXP2| exact FA2| exact SO2| exact RST2| exact BST| exact ARRr2| exact OKB2
              | exact HWL3| exact HWK3| exact LNB| exact LMNB| lia
              | exact UF| exact POST| exact FR2| exact ERR2| exact PC| eassumption| exact MU2| exact WM2] end. }
        assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
        assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 144, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
        step. if_cases KD; zify_cond KD; rewrite !signed_small in KD by lia.
        * (* [comment removed for export] *)
          ihere. to_implM. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold br.
          replace (n <=? bn_dmax br)%nat with true by (symmetry; apply Nat.leb_le; lia).
          cbn [tbind fst snd].
          eapply (CONT s bs m1 OW errv);
            [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
            | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
            | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | exact ST | exact ERR | exact MI
            | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
            | reflexivity | reflexivity | apply refs_stable_refl | fold br; lia
            | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR | exact HB'].
        * (* [comment removed for export] *)
          step. step. step.
          assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
          pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.
          pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1'.
          assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
          assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
          ihere. to_implM.
          eapply implM_embed_bind.
          { eapply (bn_expand2_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := r) (a := a) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
              [| reflexivity | exact HA | exact WR | reflexivity | reflexivity | lia].
            unfold bn_pre. rewrite ESP.
            split; [exact HEAP1|]. split; [exact LS1'|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX1|]. split; [lia|]. split; [exact B63|].
            split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
            split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
          cbv beta. intros [u bs1] st1 ms1 PO. unfold bn_post in PO. cbn [fst snd] in *.
          destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & PL2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                          & MI2 & LXP2 & FA2 & SO2 & RST2 & EPL & -> & HDM & WRES & BST). subst PL2.
          rewrite ESP in *.
          rewrite ?ret_pc_even by first [lia | reflexivity].
          assert (CLI : forall x, SRC <= x < SRC + Z.of_nat (length xs) -> lx_client LB (bv_unsigned sp + -96) (XW PL) x).
          { intros x Hx. split.
            - unfold XW. rewrite rin_ivs_app. intros [H|H].
              + revert H. unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clear - Hx BK1 BK2 BKC BKI. lia.
              + eapply (pl_frames_outside PL); [exact (proj1 FROK)| | exact H]. clear - Hx BK1 BK2 BKC CEIL LO. lia.
            - right; left. exists bk. split; [exact Hbk| lia]. }
          assert (FR2 : rw_cells bgusegs m2 (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
            intros x Hx. cbn in Hx. eapply xw_client; [exact (proj1 FROK)| lia|]. unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }
          assert (HB2 : bytes_at bgusegs m2 (SRC + Z.of_nat (length zs)) (to_bytes s')).
          { eapply bytes_at_agree; [apply agree_of_lx_pres; exact LXP2| exact HB'|]. intros x Hx. apply CLI.
            unfold to_bytes in Hx. rewrite length_map in Hx. lia. }
          unfold implM. iprefix.
          step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
          ihere. to_implM. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
          eapply (CONT st1 bs1 m2 OW2 errv2);
            [exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact MI2
            | eapply lx_pres_trans; [exact LXP1|]; eapply lx_pres_weaken; [exact LXP2| lia | intros b0 Hb0; exact Hb0 | intros a0 Ha0; exact Ha0]
            | congruence | congruence | exact RST2 | exact HDM | exact BST | exact FR2 | exact HB2].
  Qed.

  (* [comment removed for export] *)
  Lemma BN_bin2bn_walk_h : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a : Z) (D : Z) (n : list Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_BIN2BN_STACK -> tp = wz RATP ->
    ref_at bs OW PL r a -> wref PL r ->
    bytes_at bgusegs m D (to_bytes n) -> Forall (fun c => 0 <= c < 256) n -> 0 < D -> D + zlength n < 2^63 -> zlength n < 2^31 ->
    (n = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength n <= blk_addr b + blk_size b) ->
    a0 = wz D -> a1 = wz (zlength n) -> a2 = wz a ->
    implM bgusegs (interp (embed (BN_bin2bn (tree_ops bptr) n r bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz a))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xfe568) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros PRE TP HA WR HB FB D0 DH LEN HBK E0 E1 E2. unfold zlength in *.
    eapply implM_mono; [eapply (BN_bin2bn_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                   F fc m s bs OW LB PL EA lo B errv r a D n); eassumption|].
    cbv beta. intros [u bs'] st' ms' PO. unfold bn_post in *. cbn [fst snd] in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & OW' & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & _).
    do 15 eexists. exists m', OW', PL', errv'. split; [reflexivity|]. repeat (split; [assumption|]). exact P12.
  Qed.
End Proofs.
End WithCeiling0.
