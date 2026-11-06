(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition near_step (p : Z) (acc : Z) (c : Z * Z) : Z :=
  if (fst c <=? p) && (acc <? fst c) then fst c else acc.
Definition nearest (p : Z) (acc : Z) (cs : list (Z * Z)) : Z := fold_left (near_step p) cs acc.

Definition gbb_result (cs : list (Z * Z)) (p : Z) : Z :=
  let h := nearest p 0 cs in
  if h =? 0 then 0
  else match find (fun c => fst c =? h) cs with
       | Some c => if p <? fst c + snd c then fst c + 4096 else 0
       | None => 0
       end.

End RC__1.
Arguments near_step : simpl never.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma nearest_app : forall p acc l1 l2, nearest p acc (l1 ++ l2) = nearest p (nearest p acc l1) l2.
Proof. aceil. intros. unfold nearest. apply fold_left_app. Qed.

Lemma near_step_bounds : forall p acc c, 0 <= acc <= p -> 0 <= near_step p acc c <= p.
Proof. aceil.
  intros p acc c H. unfold near_step. destruct (fst c <=? p) eqn:E1; destruct (acc <? fst c) eqn:E2; cbn; lia.
Qed.

Lemma nearest_bounds : forall p cs acc, 0 <= acc <= p -> 0 <= nearest p acc cs <= p.
Proof. aceil.
  intros p cs. induction cs as [|c cs IH]; intros acc H; cbn; [exact H|].
  apply IH. apply near_step_bounds. exact H.
Qed.

Lemma nearest_in : forall p cs acc, nearest p acc cs = acc \/ In (nearest p acc cs) (map fst cs).
Proof. aceil.
  intros p cs. induction cs as [|c cs IH]; intros acc; cbn; [left; reflexivity|].
  destruct (IH (near_step p acc c)) as [E|I].
  - unfold nearest in E |- *. rewrite E. unfold near_step. destruct (_ && _); [right; left; reflexivity| left; reflexivity].
  - right. right. exact I.
Qed.

Lemma find_some_nth : forall (A : Type) (f : A -> bool) l x, find f l = Some x -> exists i, nth_error l i = Some x /\ f x = true.
Proof. aceil.
  intros A f l. induction l as [|y l IH]; intros x H; cbn in H; [discriminate|].
  destruct (f y) eqn:E.
  - injection H as ->. exists 0%nat. split; [reflexivity| exact E].
  - destruct (IH x H) as (i & Hi & Hf). exists (S i). split; [exact Hi| exact Hf].
Qed.

Lemma in_map_fst_find : forall (cs : list (Z * Z)) h, In h (map fst cs) -> exists c, find (fun c => fst c =? h) cs = Some c /\ fst c = h.
Proof. aceil.
  intros cs h. induction cs as [|c cs IH]; intros H; cbn in H; [destruct H|].
  cbn. destruct (Z.eqb_spec (fst c) h) as [E|NE].
  - exists c. split; [reflexivity| exact E].
  - destruct H as [H|H]; [exfalso; exact (NE H)|]. exact (IH H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma list_find_index_spec : forall {A} (f : A -> bool) (l : list A) (i0 : nat),
  match list_find_index f l i0 with
  | Some i => exists c, (i0 <= i)%nat /\ nth_error l (i - i0) = Some c /\ find f l = Some c
  | None => find f l = None
  end.
Proof. aceil.
  intros A f l. induction l as [|x l IH]; intros i0; cbn; [reflexivity|].
  destruct (f x) eqn:E.
  - exists x. rewrite Nat.sub_diag. cbn. repeat split; auto.
  - specialize (IH (S i0)). destruct (list_find_index f l (S i0)) as [i|]; [| exact IH].
    destruct IH as (c & Hi & Hn & Hf). exists c. split; [lia|]. split; [| exact Hf].
    replace (i - i0)%nat with (S (i - S i0))%nat by lia. cbn. exact Hn.
Qed.

Definition sec_cs (s : astate) : list (Z * Z) := map (fun c => (sc_map_beg c, sc_map_size c)) (as_sec s).

Lemma nearest_sec : forall p l acc,
  nearest p acc (map (fun c => (sc_map_beg c, sc_map_size c)) l)
  = fold_left (fun acc c => if (sc_map_beg c <=? p) && (acc <? sc_map_beg c) then sc_map_beg c else acc) l acc.
Proof. aceil.
  intros p l. induction l as [|c l IH]; intros acc; cbn; [reflexivity|].
  unfold nearest in IH |- *. cbn. rewrite <- IH. unfold near_step. cbn. reflexivity.
Qed.

Lemma find_map_pair : forall (l : list secchunk) h,
  find (fun c => fst c =? h) (map (fun c => (sc_map_beg c, sc_map_size c)) l)
  = option_map (fun c => (sc_map_beg c, sc_map_size c)) (find (fun c => sc_map_beg c =? h) l).
Proof. aceil.
  intros l h. induction l as [|c l IH]; cbn; [reflexivity|]. destruct (sc_map_beg c =? h); [reflexivity| exact IH].
Qed.

Lemma gbb_result_sec_block_begin : forall s p, gbb_result (sec_cs s) p = sec_block_begin s p.
Proof. aceil.
  intros s p. unfold gbb_result, sec_block_begin, sec_cs. rewrite nearest_sec.
  set (h := fold_left _ (as_sec s) 0). destruct (h =? 0); [reflexivity|].
  rewrite find_map_pair.
  pose proof (list_find_index_spec (fun c => sc_map_beg c =? h) (as_sec s) 0) as X.
  destruct (list_find_index _ (as_sec s) 0) as [i|].
  - destruct X as (c & _ & Hn & Hf). rewrite Nat.sub_0_r in Hn. rewrite Hn, Hf. cbn. unfold kPageSize. reflexivity.
  - rewrite X. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_cons_nth' : forall {X} (l : list X) i w, nth_error l i = Some w -> skipn i l = w :: skipn (S i) l.
Proof. aceil.
  intros X l. induction l as [|x l IH]; intros [|i] w H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - exact (IH i w H).
Qed.

Section GBBLOOP.
Variable P : acc -> Prop.
Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (mL : mem) (p PA : Z) (cs : list (Z * Z)) (junk : list word).
Definition gws : list word := map (fun c => Z_to_bv 64 (fst c)) cs ++ junk.
Hypothesis MIL : mem_inv bsegs mL.
Hypothesis HP : 0 <= p < 2^47.
Hypothesis ARRL : u64arr bsegs mL PA gws.
Hypothesis HPA : 0x603000 <= PA /\ PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= alloc_ceiling.
Hypothesis RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs.   (* [comment removed for export] *)
Hypothesis PARR : forall a n, PA <= a -> a + Z.of_nat n <= PA + 8 * Z.of_nat (length cs) -> P (Z_to_bv 64 a, n).

Notation LST pc xa2 xa3 xa5 xa6 xa7 xt0 m :=
  (MS (mkR ra sp gp tp xt0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf98) (Z_to_bv 64 p) xa2 xa3 (Z_to_bv 64 (PA + 8 * Z.of_nat (length cs))) xa5 xa6 xa7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma gbb_iter : forall (i : nat) (acc : Z) c (xa5 xa6 xa7 xt0 : word) (Q : machine_state -> Prop),
  nth_error cs i = Some c -> 0 <= acc <= p ->
  (forall xa5' xa6' xa7' xt0', evtA bsegs P Q (LST 0x34f4c (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 (near_step p acc c)) xa5' xa6' xa7' xt0' mL)) ->
  evtA bsegs P Q (LST 0x34f54 (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 acc) xa5 xa6 xa7 xt0 mL).
Proof. aceil.
  intros i acc c xa5 xa6 xa7 xt0 Q NTH HACC CONT.
  aceil.
  pose proof (nth_error_lt _ _ _ NTH) as LT.
  pose proof (proj1 (Forall_forall _ _) RNG c (nth_error_In _ _ NTH)) as (R1 & R2 & R3 & R4). aceil.
  assert (NTHW : nth_error gws (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (fst c))).
  { unfold gws. rewrite Nat2Z.id. rewrite nth_error_app1 by (rewrite length_map; exact LT). rewrite nth_error_map, NTH. reflexivity. }
  pose proof (u64arr_read bsegs mL PA gws (Z.of_nat i) (Z_to_bv 64 (fst c)) (Z_to_bv 64 (PA + 8 * Z.of_nat i)) ARRL NTHW ltac:(lia) ltac:(reflexivity)) as RD.
  zstepA. clear RD.   (* [comment removed for export] *)
  do 3 zstepA.        (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    assert (HC : fst c <= p /\ acc < fst c).
    { destruct (Z.le_gt_cases (fst c) p) as [LE|GT].
      - rewrite Z.mod_small in K1 by lia. lia.
      - exfalso. replace ((p - fst c) mod 18446744073709551616) with (18446744073709551616 + (p - fst c)) in K1 by (apply Zmod_unique with (-1); lia). lia. }
    clear K1.
    zstepA. if_cases K2; zify_cond K2. { exfalso. lia. }
    zstepA. zstepA.   (* [comment removed for export] *)
    replace (near_step p acc c) with (fst c) in CONT by (unfold near_step; destruct (Z.leb_spec (fst c) p); destruct (Z.ltb_spec acc (fst c)); cbn; lia).
    apply CONT.
  - (* [comment removed for export] *)
    assert (HC : near_step p acc c = acc).
    { unfold near_step. destruct (Z.leb_spec (fst c) p); destruct (Z.ltb_spec acc (fst c)); cbn; lia. }
    rewrite HC in CONT. clear HC K1.
    zstepA.   (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2.
    + apply CONT.
    + zstepA. zstepA. zstepA. (* [comment removed for export] *) apply CONT.
Qed.

(* [comment removed for export] *)
Lemma gbb_loop : forall (k i : nat) (acc : Z) (xa5 xa6 xa7 xt0 : word) (Q : machine_state -> Prop),
  (k + i = length cs)%nat -> (i < length cs)%nat -> 0 <= acc <= p ->
  (forall xa5' xa6' xa7' xt0', evtA bsegs P Q (LST 0x34f80 (Z_to_bv 64 (PA + 8 * Z.of_nat (length cs))) (Z_to_bv 64 (nearest p acc (skipn i cs))) xa5' xa6' xa7' xt0' mL)) ->
  evtA bsegs P Q (LST 0x34f54 (Z_to_bv 64 (PA + 8 * Z.of_nat i)) (Z_to_bv 64 acc) xa5 xa6 xa7 xt0 mL).
Proof. aceil.
  induction k as [|k IH]; intros i acc xa5 xa6 xa7 xt0 Q Hk Hi HACC CONT; [exfalso; lia|].
  aceil.
  destruct (nth_error cs i) as [c|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. lia. }
  eapply gbb_iter; [exact NTH| exact HACC|]. intros xa5' xa6' xa7' xt0'.
  assert (SKP : skipn i cs = c :: skipn (S i) cs) by (apply skipn_cons_nth'; exact NTH).
  rewrite SKP in CONT. cbn [nearest fold_left] in CONT. fold (nearest p (near_step p acc c) (skipn (S i) cs)) in CONT.
  pose proof (near_step_bounds p acc c HACC) as HB.
  zstepA.  (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (EI : (S i = length cs)%nat) by lia.
    rewrite EI, skipn_all in CONT. cbn [nearest fold_left] in CONT.
    replace (PA + 8 * Z.of_nat i + 8) with (PA + 8 * Z.of_nat (length cs)) by lia. apply CONT.
  - replace (PA + 8 * Z.of_nat i + 8) with (PA + 8 * Z.of_nat (S i)) by lia.
    eapply (IH (S i)); [lia| lia| exact HB| exact CONT].
Qed.

Lemma gbb_loop0 : forall (xa5 xa6 xa7 xt0 : word) (Q : machine_state -> Prop),
  (0 < length cs)%nat ->
  (forall xa5' xa6' xa7' xt0', evtA bsegs P Q (LST 0x34f80 (Z_to_bv 64 (PA + 8 * Z.of_nat (length cs))) (Z_to_bv 64 (nearest p 0 cs)) xa5' xa6' xa7' xt0' mL)) ->
  evtA bsegs P Q (LST 0x34f54 (Z_to_bv 64 PA) (Z_to_bv 64 0) xa5 xa6 xa7 xt0 mL).
Proof. aceil.
  intros xa5 xa6 xa7 xt0 Q Hn CONT.
  replace (Z_to_bv 64 PA) with (Z_to_bv 64 (PA + 8 * Z.of_nat 0)) by (f_equal; lia).
  eapply (gbb_loop (length cs) 0%nat 0); [lia| exact Hn| lia| exact CONT].
Qed.
End GBBLOOP.

Section GBB.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo p PA : Z) (cs : list (Z * Z)) (junk : list word).
(* [comment removed for export] *)
Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 32.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis HP : 0 <= p < 2^47.
Hypothesis SEC : rw_cells bsegs m 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA)].      (* [comment removed for export] *)
Hypothesis NCH : rw_cells bsegs m 0xaafd0 [C8 (Z_to_bv 64 (Z.of_nat (length cs)))].       (* [comment removed for export] *)
Hypothesis MTX : rw_cells bsegs m 0xab200 [C4 (Z_to_bv 64 0)].                             (* [comment removed for export] *)
Hypothesis ARR : u64arr bsegs m PA (gws cs junk).                                            (* [comment removed for export] *)
Hypothesis HPA : 0x603000 <= PA /\ PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= alloc_ceiling.
Hypothesis HDRS : forall i c, nth_error cs i = Some c ->
  exists w3 w4, rw_cells bsegs m (fst c) [C8 (Z_to_bv 64 (fst c)); C8 (Z_to_bv 64 (snd c)); C8 w3; C8 w4].
Hypothesis RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs.   (* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PARR : forall a n, PA <= a -> a + Z.of_nat n <= PA + 8 * Z.of_nat (length cs) -> P (Z_to_bv 64 a, n).
Hypothesis PHDR : forall i c a n, nth_error cs i = Some c -> fst c <= a -> a + Z.of_nat n <= fst c + 32 -> P (Z_to_bv 64 a, n).

Notation gbbW usp := [(usp - 32, usp); (0xab200, 0xab204)].

Lemma gbb_walk :
  (forall m' (a1' a2' a3' a4' a5' a6' a7' t0' : word), mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' ->
     munch (gbbW (bv_unsigned sp)) m m' ->
     rw_cells bsegs m' 0xab200 [C4 (Z_to_bv 64 0)] ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (gbb_result cs p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf98) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34ee8) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros CONT.
  aceil.
  assert (LEN : (length (gws cs junk) = length cs + length junk)%nat) by (unfold gws; rewrite length_app, length_map; reflexivity).
  assert (MU : munch (gbbW (bv_unsigned sp)) m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat SK.
  do 5 zstepA.   (* [comment removed for export] *)
  do 4 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 4 zstepA.   (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  cstep.         (* [comment removed for export] *)
  zstepA.        (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  eapply (evtA_cut bsegs P (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' t0' : word),
     ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1 t2 (Z_to_bv 64 0xab200) s1 (Z_to_bv 64 (gbb_result cs p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x34fdc) fc None mx (seg_rom bsegs))) end.
  - zstepA. if_cases K0; zify_cond K0.
    + (* [comment removed for export] *)
      assert (CS0 : cs = []) by (destruct cs; [reflexivity| cbn in K0; lia]).
      zstepA. (* [comment removed for export] *)
      apply evtA_done; cbv beta. subst cs. do 8 eexists. reflexivity.
    + do 5 zstepA. (* [comment removed for export] *)
      rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length cs)) 3) by lia.
      replace (PA + Z.of_nat (length cs) * 2 ^ 3) with (PA + 8 * Z.of_nat (length cs)) by lia.
      eapply (gbb_loop0 P);
        [exact HP| exact ARR| aceil; lia| exact RNG| exact PARR| lia|].
      intros xa5 xa6 xa7 xt0.
      pose proof (nearest_bounds p cs 0 ltac:(lia)) as NB.
      zstepA. if_cases K1; zify_cond K1; try rewrite Z.mod_small in K1 by lia.
      * (* [comment removed for export] *)
        zstepA. (* [comment removed for export] *)
        apply evtA_done; cbv beta.
        replace (gbb_result cs p) with 0 by (unfold gbb_result; rewrite (proj2 (Z.eqb_eq _ _) K1); reflexivity).
        do 8 eexists. reflexivity.
      * (* [comment removed for export] *)
        destruct (nearest_in p cs 0) as [E0|IN]; [exfalso; lia|].
        destruct (in_map_fst_find cs _ IN) as (c & FD & Ec).
        destruct (find_some_nth _ _ cs c FD) as (ic & NTH & _).
        pose proof (proj1 (Forall_forall _ _) RNG c (nth_error_In _ _ NTH)) as (R1 & R2 & R3 & R4). aceil.
        destruct (HDRS ic c NTH) as (w3 & w4 & HC).
        eapply rw_cells_transport in HC; [| exact MU| exact WM| cbn; lia].
        rewrite <- Ec.
        zstepA. (* [comment removed for export] *)
        zstepA. if_cases K2; zify_cond K2. { exfalso. lia. }
        zstepA. (* [comment removed for export] *)
        zstepA. (* [comment removed for export] *)
        zstepA. if_cases K3; zify_cond K3. { exfalso. lia. }
        zstepA. if_cases K4; zify_cond K4. { exfalso. lia. }
        zstepA. if_cases K5; zify_cond K5.
        -- (* [comment removed for export] *)
           zstepA. (* [comment removed for export] *)
           apply evtA_done; cbv beta.
           replace (gbb_result cs p) with 0.
           2:{ unfold gbb_result. rewrite <- Ec in FD |- *. destruct (Z.eqb_spec (fst c) 0); [exfalso; lia|]. rewrite FD.
               destruct (Z.ltb_spec p (fst c + snd c)); [exfalso; lia| reflexivity]. }
           do 8 eexists. reflexivity.
        -- zstepA. (* [comment removed for export] *)
           zstepA. (* [comment removed for export] *)
           zstepA. (* [comment removed for export] *)
           replace (Z.land 4095 (fst c)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096; lia).
           cstep.  (* [comment removed for export] *)
           zstepA. (* [comment removed for export] *)
           zstepA. (* [comment removed for export] *)
           apply evtA_done; cbv beta.
           replace (gbb_result cs p) with (4096 + fst c).
           2:{ unfold gbb_result. rewrite <- Ec in FD |- *. destruct (Z.eqb_spec (fst c) 0); [exfalso; lia|]. rewrite FD.
               destruct (Z.ltb_spec p (fst c + snd c)); [lia| exfalso; lia]. }
           do 8 eexists. reflexivity.
  - (* [comment removed for export] *)
    clear HDRS PHDR PARR ARR.
    intros ms' (xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt0 & ->).
    assert (MTXB : rw_cells bsegs m0 0xab200 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)]).
    { eapply rw_cells_reshape; [| | exact MTX]; [cbn; tauto| vm_compute; reflexivity]. }
    clear MTX.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (MTX' : rw_cells bsegs mx 0xab200 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
    clear MTXB.
    do 5 zstepA. (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp).
    zstepA. (* [comment removed for export] *)
    eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact MTX'].
Qed.
End GBB.
End RC__2.
