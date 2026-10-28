(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ShadowTac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition istrlen_entry := 0x66054%Z.
Definition istrchr_entry := 0x65fb4%Z.
Definition imemset_entry := 0x65f00%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition istrlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Section Strlen.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis STR : bytes_at bsegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m).

  Lemma istrlen_loop : forall (k : nat) (i : Z) x12,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 i) x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x66058) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    induction k as [|k IH]; intros i x12 Hk Hi.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read bsegs m A _ len (Z_to_bv 8 0) _ STR ltac:(rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. fold_lits. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrlen_post. finish.
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      assert (Hb : bv_unsigned b <> 0%Z). { rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto. }
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      pose proof (u8ro_read bsegs m A _ i b _ STR ltac:(rewrite nth_error_app1 by lia; exact E) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      apply IH; lia.
  Qed.

  Lemma istrlen_body :
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x66054) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    zstep. apply (istrlen_loop (Z.to_nat len) 0); lia.
  Qed.
End Strlen.

Lemma istrlen_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte),
  mem_inv bsegs m ->
  bytes_at bsegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF bsegs RNG (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x66054) fc None m (seg_rom bsegs)).
Proof. intros. eapply istrlen_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' => if (bv_unsigned b =? c)%Z then Some 0%nat else option_map S (find_byte c l')
  end.

Definition istrchr_res (A : Z) (str : list byte) (c : Z) : Z :=
  match find_byte c str with Some i => (A + Z.of_nat i)%Z | None => 0%Z end.

Lemma find_byte_Some : forall c l i, find_byte c l = Some i ->
  (i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
  forall j b, (j < i)%nat -> nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned b) c).
  - injection H as <-. cbn. split; [lia|]. split; [eauto|]. intros; lia.
  - destruct (find_byte c l) as [i0|] eqn:E; cbn in H; [|discriminate]. injection H as <-.
    destruct (IH i0 eq_refl) as (L & (b0 & Hn & Hc) & NO). cbn. split; [lia|]. split; [eauto|].
    intros [|j] b' Hj Hn'; cbn in Hn'. { injection Hn' as <-. exact n. } eapply NO; [|exact Hn']. lia.
Qed.

Lemma find_byte_None : forall c l, find_byte c l = None -> forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros H j b' Hn; [destruct j; discriminate|].
  cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c); [discriminate|].
  destruct (find_byte c l) eqn:E; [discriminate|].
  destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact n. } eapply IH; eauto.
Qed.

Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : Z) (str : list byte) (c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (istrchr_res A str c)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Section Strchr.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte) (c : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis STR : bytes_at bsegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis C : a1 = Z_to_bv 64 c.
  Hypothesis CR : (0 < c < 256)%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ (Z_to_bv 8 0) :: rest).
  Notation POST := (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m).

  Lemma full_nth : forall i, (0 <= i <= len)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\
     (i < len -> nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0)%Z /\ (i = len -> b = Z_to_bv 8 0).
  Proof.
    intros i Hi. destruct (Z.eq_dec i len) as [->|].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. cbn. split; [reflexivity|]. split; [lia| auto].
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [|lia]. intros _. split; [reflexivity|].
      rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma istrchr_loop : forall (k : nat) (i : Z) (b : byte) x10 x11,
    x10 = Z_to_bv 64 (A + i) ->
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    nth_error full (Z.to_nat i) = Some b -> bv_unsigned b <> c ->
    (forall j b', (j <= Z.to_nat i)%nat -> nth_error str j = Some b' -> bv_unsigned b' <> c) ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65fc4) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    induction k as [|k IH]; intros i b x10 x11 -> Hk Hi Hn Hc NO.
    - assert (Ei : i = len) by lia. subst i.
      rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag in Hn by lia. cbn in Hn. injection Hn as <-.
      zstep. if_cases K; zify_cond K. 2:{ exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrchr_post, istrchr_res.
      destruct (find_byte c str) as [i0|] eqn:FB.
      { exfalso. destruct (find_byte_Some _ _ _ FB) as (L & (b0 & Hb0 & Hc0) & _). eapply NO; [|exact Hb0| exact Hc0]. lia. }
      finish.
    - destruct (full_nth i ltac:(lia)) as (b0 & Hn0 & Hlt & _). rewrite Hn in Hn0. injection Hn0 as <-.
      destruct (Hlt ltac:(lia)) as [Hstr Hb0].
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      zstep. if_cases K; zify_cond K. { exfalso. lia. }
      destruct (full_nth (i + 1) ltac:(lia)) as (b1 & Hn1 & Hlt1 & Heq1).
      pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb1.
      pose proof (u8ro_read bsegs m A _ (i + 1) b1 _ STR Hn1 ltac:(lia) eq_refl) as RD.
      zstep. cbv beta. zsimp. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (IH (i + 1)%Z b1); [f_equal; lia | lia | lia | assumption | lia |].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (i + 1))).
        * subst j. destruct (Z.eq_dec (i + 1) len) as [E|].
          { exfalso. apply nth_error_some_bound in Hn'. lia. } 
          destruct (Hlt1 ltac:(lia)) as [Hs1 _]. rewrite Hs1 in Hn'. injection Hn' as <-. lia.
        * eapply NO; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. zstep. unfold istrchr_post, istrchr_res.
        assert (FB : find_byte c str = Some (Z.to_nat (i + 1))).
        { destruct (find_byte c str) as [i0|] eqn:FB.
          - destruct (find_byte_Some _ _ _ FB) as (L & (bb & Hbb & Hcc) & NOi).
            destruct (Nat.lt_trichotomy i0 (Z.to_nat (i + 1))) as [Hl|[He|Hg]].
            + exfalso. eapply NO; [|exact Hbb|exact Hcc]. lia.
            + rewrite He. reflexivity.
            + exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
              { lia. }
              destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply NOi; [exact Hg| exact Hs1| lia].
          - exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
            { rewrite (Heq1 E) in K2. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K2. lia. }
            destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply (find_byte_None _ _ FB); [exact Hs1| lia]. }
        rewrite FB. replace (A + Z.of_nat (Z.to_nat (i + 1)))%Z with (A + i + 1)%Z by lia. finish.
  Qed.

  Lemma istrchr_body :
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65fb4) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM. subst a1.
    destruct (full_nth 0 ltac:(lia)) as (b0 & Hn0 & Hlt0 & Heq0).
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb0.
    pose proof (u8ro_read bsegs m A _ 0 b0 _ STR Hn0 ltac:(lia) eq_refl) as RD.
    replace (wa (A + 0)) with a0 in RD by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    zstep. cbv beta. zsimp. zstep.
    replace (Z.land c 255) with c by (change 255%Z with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    zstep. if_cases K; zify_cond K.
    - eapply (istrchr_loop (Z.to_nat len) 0 b0); [rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | exact Hn0 | lia |].
      intros j b' Hj Hn'. assert (j = 0%nat) by lia. subst j.
      destruct (Z.eq_dec 0 len) as [E|]. { exfalso. apply nth_error_some_bound in Hn'. lia. }
      destruct (Hlt0 ltac:(lia)) as [Hs _]. change (Z.to_nat 0) with 0%nat in Hs. rewrite Hs in Hn'. injection Hn' as <-. lia.
    - zstep. unfold istrchr_post, istrchr_res.
      assert (FB : find_byte c str = Some 0%nat).
      { destruct (Z.eq_dec 0 len) as [E|]. { rewrite (Heq0 E) in K. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K. lia. }
        destruct (Hlt0 ltac:(lia)) as [Hs _]. destruct str as [|bb l]; [discriminate|]. cbn in Hs. injection Hs as ->.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) K). reflexivity. }
      rewrite FB. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (Z_to_bv 64 A) with a0 by (symmetry; apply Z_to_bv_bv_unsigned). finish.
  Qed.
End Strchr.

Lemma istrchr_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte) (c : Z),
  mem_inv bsegs m ->
  bytes_at bsegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  a1 = Z_to_bv 64 c -> (0 < c < 256)%Z ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF bsegs RNG (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65fb4) fc None m (seg_rom bsegs)).
Proof. intros. eapply istrchr_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma list_all_repeat : forall {X} (l : list X) (x : X) k,
  length l = k -> (forall j, (j < k)%nat -> nth_error l j = Some x) -> l = repeat x k.
Proof.
  intros X l x k Hl H. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j k).
  - rewrite H, nth_error_repeat by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l j)) by lia. rewrite (proj2 (nth_error_None _ j)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma lor_land15_ne : forall n x, (0 <= n)%Z -> (0 <= x)%Z -> Z.land n 15 <> 0%Z -> Z.land (Z.lor n x) 15 <> 0%Z.
Proof.
  intros n x Hn Hx H. rewrite Z.land_lor_distr_l. intros E. apply Z.lor_eq_0_iff in E. lia.
Qed.

Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' (bv_unsigned a0) (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

Section Memset.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (junk : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis DST : u8arr bsegs m (bv_unsigned a0) junk.
  Hypothesis LEN : length junk = Z.to_nat n.
  Hypothesis N : a2 = Z_to_bv 64 n.
  Hypothesis NR : (1 <= n)%Z.
  Hypothesis NB : (bv_unsigned a0 + n < 2^64)%Z.
  Hypothesis BYTEPATH : Z.land n 15 <> 0%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) n.
  Notation D := (bv_unsigned a0).
  Notation cb := (Z_to_bv 8 (bv_unsigned a1)).
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n).

  (* [comment removed for export] *)
  Lemma imemset_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr bsegs mc D bs -> length bs = Z.to_nat n -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = Some cb) ->
    munch [(D, D + n)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65f18) fc None mc (seg_rom bsegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    induction k as [|k IH]; intros i mc bs Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    pose proof (u8arr_store_ok bsegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write bsegs mc D bs i cb ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 a1) with [cb].
    store_done.
    zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite upd_length; exact LBS | | assumption | assumption | assumption].
      intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
      + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
      + rewrite nth_error_upd_other by lia. apply DONE. lia.
    - zstep. zstep. unfold imemset_post.
      assert (E : upd bs (Z.to_nat i) cb = repeat cb (Z.to_nat n)).
      { apply list_all_repeat. { rewrite upd_length; exact LBS. }
        intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
        + rewrite nth_error_upd_other by lia. apply DONE. lia. }
      rewrite E in ARR'. finish.
  Qed.

  Lemma imemset_body :
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65f00) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM. subst a2.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    { exfalso. apply (lor_land15_ne n D); try lia; first [exact K | rewrite Z.lor_comm; exact K]. }
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 2 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    eapply (imemset_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
  Qed.
End Memset.


Lemma imemset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z) (junk : list byte),
  mem_inv bsegs m ->
  u8arr bsegs m (bv_unsigned a0) junk -> length junk = Z.to_nat n ->
  a2 = Z_to_bv 64 n -> (1 <= n)%Z -> (bv_unsigned a0 + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG (bv_unsigned a0) n ->
  evtF bsegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65f00) fc None m (seg_rom bsegs)).
Proof. intros. eapply imemset_body; eassumption. Qed.

(* [comment removed for export] *)
Definition imemset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (D n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u8arr bsegs m' D (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

Lemma imemset_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
  mem_inv bsegs m ->
  u8arr bsegs m D junk -> length junk = Z.to_nat n ->
  (1 <= n)%Z -> (0 <= D)%Z -> (D + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG D n ->
  evtF bsegs RNG (imemset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 m D n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65f00) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI DST LEN NR D0 NB BP RR.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemset_post in P. rewrite !U in P. exact P.
Qed.
End CANSEC1.
