(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs.
(* [comment removed for export] *)
Ltac2 Set StepFast.sf_fold := Ltac2.Init.false.


Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition MM_M : Z := 0xc6a4a7935bd1e995.
Definition MM_SEED : Z := 0x9747b28c9747b28c.
Definition MM_M8 : Z := 0x35253c9ade8f4ca8.
Definition W64 : Z := 18446744073709551616.

Definition mm_step (v x : Z) : Z :=
  (Z.lxor ((Z.lxor (Z.shiftr ((x * MM_M) mod W64) 47) ((x * MM_M) mod W64) * MM_M) mod W64) v * MM_M) mod W64.
Fixpoint mm_loop (v : Z) (l : list Z) : Z :=
  match l with [] => v | x :: l' => mm_loop (mm_step v x) l' end.
Definition mm_fin (w : Z) : Z :=
  let y := ((Z.lxor (Z.shiftr w 47) w) * MM_M) mod W64 in Z.lxor (Z.shiftr y 47) y.
Definition mm_init (n : Z) : Z := Z.lxor ((n * MM_M8) mod W64) MM_SEED.
Definition depot_hash (T : list Z) : Z :=
  mm_fin (mm_step (mm_loop (mm_init (Z.of_nat (length T))) T) 0).

Goal depot_hash [0x7e0c4; 0x7f414] = 877684846266345625 /\ depot_hash [0x7e0c4] = 7701145002419118861
     /\ depot_hash [0x098004; 0x0caaac; 0x0c6b98; 0x0c6530] = 3252010087649400781.   (* [comment removed for export] *)
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma mm_fin_range : forall w, 0 <= mm_fin w < W64.
Proof.
  intros w. unfold mm_fin. cbv zeta. set (y := (Z.lxor (Z.shiftr w 47) w * MM_M) mod W64).
  assert (Hy : inr64 y). { unfold inr64, y. apply Z.mod_pos_bound. reflexivity. }
  change W64 with (2^64). apply zr_lxor; [apply zr_shiftr; [exact Hy|lia] | exact Hy].
Qed.
Lemma depot_hash_range : forall T, 0 <= depot_hash T < 2^64.
Proof. intros T. unfold depot_hash. apply mm_fin_range. Qed.

Lemma mm_step_range : forall v x, 0 <= mm_step v x < W64.
Proof. intros. unfold mm_step. apply Z.mod_pos_bound. reflexivity. Qed.
Lemma mm_loop_range : forall l v, 0 <= v < W64 -> 0 <= mm_loop v l < W64.
Proof. induction l as [|x l IH]; intros v Hv; cbn; [exact Hv|apply IH, mm_step_range]. Qed.
Lemma mm_init_range : forall n, 0 <= mm_init n < W64.
Proof.
  intros n. unfold mm_init. pose proof (Z.mod_pos_bound (n * MM_M8) W64 eq_refl) as H.
  change W64 with (2^64) in *. apply (zr_lxor _ _ H). unfold inr64, MM_SEED. lia.
Qed.

Lemma skipn_S_of_cons : forall {X} (T : list X) n x l, skipn n T = x :: l -> skipn (S n) T = l.
Proof.
  intros X T n x l E. change (S n) with (1 + n)%nat. rewrite <- skipn_skipn, E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HashCode.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (TR : Z) (T : list Z) (rest : list word).
  Variable n : Z.
  Hypothesis NT : n = Z.of_nat (length T).
  Hypothesis BUF : u64arr asegs m TR (map wz T ++ rest).
  Hypothesis TRR : 0 < TR /\ TR + 8 * n <= 2^64.
  Hypothesis RNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis MI : mem_inv asegs m.

  Lemma hash_loop_code : forall (l : list Z) (i v : Z) Q
      (x5 x6 x7 x8 x9 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    skipn (Z.to_nat i) T = l -> l <> [] -> 0 <= i -> 0 <= v < W64 ->
    (forall a5 a6, evt asegs Q (MS (mkR ra sp gp tp x5 x6 x7 x8 x9 (wz MM_M) (wz (TR + 8 * n)) (wz (mm_loop v l)) x13 (wz (TR + 8 * n)) a5 a6
                                        x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                   F (Z_to_bv 64 0x1e1250) fc None m (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp x5 x6 x7 x8 x9 (wz MM_M) (wz (TR + 8 * i)) (wz v) x13 (wz (TR + 8 * n)) x15 x16
                     x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0x1e122c) fc None m (seg_rom asegs)).
  Proof.
    induction l as [|x l IH]; intros i v Q x5 x6 x7 x8 x9 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SK NE I0 VR K.
    { congruence. }
    assert (IL : (Z.to_nat i < length T)%nat).
    { destruct (Nat.lt_ge_cases (Z.to_nat i) (length T)) as [L|L]; [exact L|]. rewrite skipn_all2 in SK by lia. discriminate. }
    assert (NX : nth_error (map wz T ++ rest) (Z.to_nat i) = Some (wz x)).
    { rewrite nth_error_app1 by (rewrite length_map; lia). rewrite nth_error_map.
      replace (nth_error T (Z.to_nat i)) with (hd_error (skipn (Z.to_nat i) T)) by (clear; revert T; induction (Z.to_nat i); intros [|? ?]; cbn; auto).
      rewrite SK. reflexivity. }
    assert (XR : 0 <= x < 2^64).
    { apply (Forall_forall _ _) with (x := x) in RNG; [exact RNG|]. rewrite <- (firstn_skipn (Z.to_nat i) T), SK. apply in_or_app. right. left. reflexivity. }
    pose proof (u64arr_read asegs _ _ _ i (wz x) (wa (TR + 8 * i)) BUF NX I0 eq_refl) as HR.
    unfold wz, MM_M, W64 in *.
    step. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some (Z_to_bv 64 (Z.lxor ?K3 v * 14313749767032793493))] =>
        replace (Z_to_bv 64 (Z.lxor K3 v * 14313749767032793493)) with (Z_to_bv 64 (mm_step v x))
          by (unfold mm_step, MM_M, W64; apply Z_to_bv_mod64) end end.
    step. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      pose proof (skipn_S_of_cons _ _ _ _ SK) as SK'.
      destruct l as [|y l']. { exfalso. pose proof (skipn_length (S (Z.to_nat i)) T) as L. rewrite SK' in L. cbn in L. lia. }
      replace (TR + 8 * i + 8) with (TR + 8 * (i + 1)) by lia.
      apply (IH (i + 1) (mm_step v x)); try assumption.
      + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact SK'.
      + discriminate.
      + lia.
      + apply mm_step_range.
    - (* [comment removed for export] *)
      assert (E : l = []).
      { pose proof (skipn_S_of_cons _ _ _ _ SK) as SK'. rewrite skipn_all2 in SK' by lia. congruence. }
      subst l. cbn [mm_loop] in K.
      replace (TR + 8 * i + 8) with (TR + 8 * n) by lia.
      apply K.
  Qed.

  Lemma hash_phase_code : forall Q (x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    1 <= n < 2^32 ->
    (forall a0 a1 a2 a4 a5 a6,
       evt asegs Q (MS (mkR ra sp gp tp x5 x6 x7 x8 x9 a0 a1 a2 (wz 0x400000) a4 a5 a6 x17 x18 (wz (depot_hash T)) x20 x21
                        (wz 0xffff) (wz 0x7fffffff) x24 x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x1e1290) fc None m (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp x5 x6 x7 x8 x9 x10 (wz TR) (wz n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0x1e11f4) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros NR K. unfold wz in *.
    zstep. rewrite Z.shiftr_div_pow2, Z.div_small by lia.
    step. step. step. zstep. step. zstep.
    change 4294967295 with (2^32 - 1). rewrite zb_land_mask, Z.mod_small by lia.
    step. step. step. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. zstep. zstep.
    replace (TR + n * 8) with (TR + 8 * n) by lia.
    destruct T as [|t0_ T'] eqn:ET. { exfalso. cbn in NT. lia. }
    rewrite <- ET in *.
    replace (Z_to_bv 64 TR) with (Z_to_bv 64 (TR + 8 * 0)) by (f_equal; lia).
    apply (hash_loop_code T 0 (mm_init n)).
    { reflexivity. } { rewrite ET. discriminate. } { lia. } { apply mm_init_range. }
    intros a5_ a6_. unfold wz, MM_M in *.
    step. step. zstep. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (Z.mod_small (mm_loop (mm_init n) T) 18446744073709551616) by (apply mm_loop_range, mm_init_range).
    match goal with |- context [Some (Z_to_bv 64 (Z.lxor (Z.shiftr ?Y 47) ?Y))] =>
      replace (Z_to_bv 64 (Z.lxor (Z.shiftr Y 47) Y)) with (Z_to_bv 64 (depot_hash T))
        by (unfold depot_hash, mm_fin, mm_step, MM_M, W64; rewrite <- NT; reflexivity) end.
    apply K.
  Qed.
End HashCode.
