(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Stage1Model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Module S2G.
Section WithSegs.
Context {fx : FPState}.
Variable SEGS : list Segment.

Definition mem : Type := word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rdZ (M : mem) (a : Z) (n : nat) : option Z :=
  match rdn SEGS M (Z_to_bv 64 a) n with Some bs => Some (bytes_le_to_Z bs) | None => None end.
Definition u32_at (M : mem) (a : Z) : option Z := rdZ M a 4.
Definition u32v (M : mem) (a : Z) : Z := match u32_at M a with Some v => v | None => 0 end.
(* [comment removed for export] *)
Definition input (M : mem) (buf len : Z) : option (list Z) :=
  match rdn SEGS M (Z_to_bv 64 buf) (Z.to_nat (len + 64)) with Some bs => Some (map bv_unsigned bs) | None => None end.
Definition nthb (bs : list Z) (i : Z) : Z := if i <? 0 then 0 else nth (Z.to_nat i) bs 0.

(* [comment removed for export] *)
Definition idxm (M : mem) (a1 n len k : Z) : Z := if k <? n then u32v M (a1 + 4 * k) else len.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition p_s1ok (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; n] =>
      0 <= len /\ buf + len + 64 < two64 /\ a1 + 4 * n + 12 < two64 /\ 1 <= n /\
      exists bs, input M buf len = Some bs /\
      snd (S1M.result (nthb bs) len) = S1M.SUCCESS /\ Z.of_nat (length (fst (S1M.result (nthb bs) len))) = n /\ nthb bs len = 0 /\
      (forall k, (k < length (fst (S1M.result (nthb bs) len)))%nat ->
         u32_at M (a1 + 4 * Z.of_nat k) = Some (nth k (fst (S1M.result (nthb bs) len)) 0)) /\
      u32_at M (a1 + 4 * n) = Some len /\ u32_at M (a1 + 4 * n + 4) = Some len /\ u32_at M (a1 + 4 * n + 8) = Some 0
  | _ => False
  end.

(* [comment removed for export] *)
Definition p_str (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; n; k; p] =>
      0 <= len /\ buf + len + 64 < two64 /\ a1 + 4 * n + 12 < two64 /\ 1 <= k <= n /\
      exists bs x j fq' fq, input M buf len = Some bs /\ u32_at M (a1 + 4 * (k - 1)) = Some x /\ nthb bs x = 34 /\
        S1M.qsearch (nthb bs) fq' (x + 1) = Some j /\ p <= j /\ j < len /\ S1M.qsearch (nthb bs) fq p = Some j
  | _ => False
  end.

Definition p_acc (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [a1; n; len; k; t; s; tb; sb] =>
      0 <= n /\ a1 + 4 * n + 12 < two64 /\ k <= n + 1 /\
      t + tb <= idxm M a1 n len k + 2 /\ 3 * s <= 5 * idxm M a1 n len k + sb
  | _ => False
  end.

Definition p_ocinv (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [oc; dd; t] => 0 <= dd /\ oc + 8 * dd + 8 < two64 /\
                   forall d, 0 <= d <= dd -> exists v, u32_at M (oc + 8 * d) = Some v /\ v + 1 <= t
  | _ => False
  end.

(* [comment removed for export] *)
Definition u8_at (M : mem) (a : Z) : option Z := rdZ M a 1.
Definition p_iab (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [ia; dd] => 0 <= dd /\ ia + dd + 1 < two64 /\
               forall d, 1 <= d <= dd -> exists v, u8_at M (ia + d) = Some v /\ v <= 1
  | _ => False
  end.

(* [comment removed for export] *)
Definition GP2 (id : nat) (vs : list Z) (M : mem) : Prop :=
  if Nat.eqb id 60 then p_s1ok vs M
  else if Nat.eqb id 61 then p_str vs M
  else if Nat.eqb id 62 then p_acc vs M
  else if Nat.eqb id 64 then p_ocinv vs M
  else if Nat.eqb id 65 then p_iab vs M
  else False.

(* [comment removed for export] *)
Definition len4n12 (n : expr) : expr := mkAlu ALU_ADD (mkAlu ALU_SLL n (ELit 2)) (ELit 12).
Definition fp_s1ok (args : list expr) : list (expr * expr) :=
  match args with [buf; len; a1; n] => [(buf, mkAlu ALU_ADD len (ELit 64)); (a1, len4n12 n)] | _ => [(ELit 0, ELit 0)] end.
Definition fp_str (args : list expr) : list (expr * expr) :=
  match args with [buf; len; a1; n; k; p] => [(buf, mkAlu ALU_ADD len (ELit 64)); (a1, len4n12 n)] | _ => [(ELit 0, ELit 0)] end.
Definition fp_acc (args : list expr) : list (expr * expr) :=
  match args with [a1; n; len; k; t; s; tb; sb] => [(a1, len4n12 n)] | _ => [(ELit 0, ELit 0)] end.
(* [comment removed for export] *)
Definition fp_ocinv (args : list expr) : list (expr * expr) :=
  match args with [oc; dd; t] => [(oc, mkAlu ALU_ADD (mkAlu ALU_SLL dd (ELit 3)) (ELit 4))] | _ => [(ELit 0, ELit 0)] end.
(* [comment removed for export] *)
Definition fp_iab (args : list expr) : list (expr * expr) :=
  match args with [ia; dd] => [(ia, mkAlu ALU_ADD dd (ELit 1))] | _ => [(ELit 0, ELit 0)] end.
(* [comment removed for export] *)
Definition fp2 (id : nat) (args : list expr) : list (expr * expr) :=
  if Nat.eqb id 60 then fp_s1ok args
  else if Nat.eqb id 61 then fp_str args
  else if Nat.eqb id 62 then fp_acc args
  else if Nat.eqb id 64 then fp_ocinv args
  else if Nat.eqb id 65 then fp_iab args
  else [(ELit 0, ELit 0)].
Definition GPAR2 (vcs : list vc) : gparams := GPAR fp2 (AP.vc_list vcs).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition agree_on (M M' : mem) (a : Z) (n : Z) : Prop :=
  forall x : word, a <= bv_unsigned x < a + n -> M' x = M x.

Lemma rdn_frame : forall M M' a n, 0 <= a -> a + Z.of_nat n <= two64 -> agree_on M M' a (Z.of_nat n) ->
  rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' a n Ha Hn Hag. unfold two64 in Hn. destruct n as [|n']; [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
  apply rdn_ext; [rewrite Hu; lia|]. intros x Hx. apply Hag. rewrite Hu in Hx. lia.
Qed.
Lemma rdZ_frame : forall M M' a n, 0 <= a -> a + Z.of_nat n <= two64 -> agree_on M M' a (Z.of_nat n) -> rdZ M' a n = rdZ M a n.
Proof. intros M M' a n Ha Hn Hag. unfold rdZ. rewrite (rdn_frame M M' a n Ha Hn Hag). reflexivity. Qed.
Lemma u32_at_frame : forall M M' a, 0 <= a -> a + 4 <= two64 -> agree_on M M' a 4 -> u32_at M' a = u32_at M a.
Proof. intros M M' a Ha Hn Hag. unfold u32_at. apply rdZ_frame; [lia | exact Hn | exact Hag]. Qed.
Lemma input_frame : forall M M' buf len, 0 <= buf -> 0 <= len -> buf + len + 64 <= two64 -> agree_on M M' buf (len + 64) ->
  input M' buf len = input M buf len.
Proof.
  intros M M' buf len Hb Hl Hn Hag. unfold input.
  rewrite (rdn_frame M M' buf (Z.to_nat (len + 64)) Hb ltac:(rewrite Z2Nat.id; lia) ltac:(rewrite Z2Nat.id; [exact Hag|lia])).
  reflexivity.
Qed.
Lemma agree_on_sub : forall M M' a n a' n', agree_on M M' a n -> a <= a' -> a' + n' <= a + n -> agree_on M M' a' n'.
Proof. intros M M' a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma in_fp_range1 : forall E b n a,
  APS.in_fp E [(b, n)] a = true <-> (bv_unsigned (edenot E b) <= bv_unsigned a < bv_unsigned (edenot E b) + bv_unsigned (edenot E n)).
Proof.
  intros E b n a. unfold APS.in_fp. cbn [existsb fst snd]. unfold estart, elenZ. cbn [a_base a_off].
  rewrite Bool.orb_false_r, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. lia.
Qed.
Lemma in_fp_range2 : forall E b n b' n' a,
  APS.in_fp E [(b, n); (b', n')] a = true <->
  ((bv_unsigned (edenot E b) <= bv_unsigned a < bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) \/
   (bv_unsigned (edenot E b') <= bv_unsigned a < bv_unsigned (edenot E b') + bv_unsigned (edenot E n'))).
Proof.
  intros E b n b' n' a. unfold APS.in_fp. cbn [existsb fst snd]. unfold estart, elenZ. cbn [a_base a_off].
  rewrite Bool.orb_false_r, Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.


Notation uD E e := (bv_unsigned (edenot E e)) (only parsing).
Lemma uE_add_lit : forall E e c, 0 <= c -> uD E e + c < two64 -> uD E (mkAlu ALU_ADD e (ELit c)) = uD E e + c.
Proof.
  intros E e c Hc H. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64a.
  pose proof (u64_range (edenot E e)). unfold two64 in H. rewrite (Z.mod_small c) by lia. apply Z.mod_small. lia.
Qed.
Lemma uE_sll_lit : forall E e s, 0 <= s < 64 -> uD E e * 2 ^ s < two64 -> uD E (mkAlu ALU_SLL e (ELit s)) = uD E e * 2 ^ s.
Proof.
  intros E e s Hs H. rewrite mkAlu_denot, u_sll64. cbn [edenot]. rewrite u_lit64a.
  pose proof (u64_range (edenot E e)). unfold two64 in H. rewrite (Z.mod_small s) by lia. rewrite (Z.mod_small s) by lia.
  apply Z.mod_small. lia.
Qed.
Lemma uE_len4n12 : forall E n, uD E n * 4 + 12 < two64 -> uD E (len4n12 n) = uD E n * 4 + 12.
Proof.
  intros E n H. unfold len4n12. pose proof (u64_range (edenot E n)) as Hr.
  rewrite uE_add_lit; [|lia|rewrite uE_sll_lit; [unfold two64 in *; lia|lia|change (2^2) with 4; lia]].
  rewrite uE_sll_lit; [change (2^2) with 4; lia|lia|change (2^2) with 4; lia].
Qed.
Lemma uE_len8d4 : forall E d, uD E d * 8 + 8 < two64 ->
  uD E (mkAlu ALU_ADD (mkAlu ALU_SLL d (ELit 3)) (ELit 4)) = uD E d * 8 + 4.
Proof.
  intros E d H. pose proof (u64_range (edenot E d)) as Hr.
  rewrite uE_add_lit; [|lia|rewrite uE_sll_lit; [unfold two64 in *; lia|lia|change (2^3) with 8; lia]].
  rewrite uE_sll_lit; [change (2^3) with 8; lia|lia|change (2^3) with 8; lia].
Qed.

(* [comment removed for export] *)
Theorem GP2_frame : forall id args E M M',
  (forall a, APS.in_fp E (fp2 id args) a = true -> M' a = M a) ->
  GP2 id (map (APS.uE E) args) M -> GP2 id (map (APS.uE E) args) M'.
Proof.
  intros id args E M M' Hfp H. unfold GP2, fp2 in *.
  destruct (Nat.eqb id 60).
  { (* [comment removed for export] *) unfold p_s1ok, fp_s1ok in *.
    destruct args as [|buf [|len [|a1 [|n [|? ?]]]]]; cbn [map] in *; try contradiction.
    destruct H as (Hl & Hb & Ha & Hn & bs & Hin & Hrest). pose proof (u64_range (edenot E buf)) as Hb0. pose proof (u64_range (edenot E a1)) as Ha0.
    unfold APS.uE in *.
    assert (AG1 : agree_on M M' (bv_unsigned (edenot E buf)) (bv_unsigned (edenot E len) + 64)).
    { intros x Hx. apply Hfp. apply (proj2 (in_fp_range2 E _ _ _ _ x)). left.
      rewrite uE_add_lit; lia. }
    assert (AG2 : agree_on M M' (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E n) * 4 + 12)).
    { intros x Hx. apply Hfp. apply (proj2 (in_fp_range2 E _ _ _ _ x)). right.
      rewrite uE_len4n12; lia. }
    repeat split; try assumption. exists bs. split; [rewrite <- Hin; apply input_frame; try lia; exact AG1|].
    destruct Hrest as (R1 & R2 & R0 & R3 & R4 & R5 & R6). split; [exact R1|]. split; [exact R2|]. split; [exact R0|].
    split; [|split; [|split]].
    - intros k Hk. rewrite <- (R3 k Hk). apply u32_at_frame; [lia| unfold two64 in *; lia |]. eapply agree_on_sub; [exact AG2|lia|lia].
    - rewrite <- R4. apply u32_at_frame; [lia|unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG2|lia|lia].
    - rewrite <- R5. apply u32_at_frame; [lia|unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG2|lia|lia].
    - rewrite <- R6. apply u32_at_frame; [lia|unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG2|lia|lia]. }
  destruct (Nat.eqb id 61).
  { (* [comment removed for export] *) unfold p_str, fp_str in *.
    destruct args as [|buf [|len [|a1 [|n [|k [|p [|? ?]]]]]]]; cbn [map] in *; try contradiction.
    destruct H as (Hl & Hb & Ha & Hk & bs & x & j & fq' & fq & Hin & Hx & H34 & Hq' & Hj & Hjl & Hq).
    pose proof (u64_range (edenot E buf)) as Hb0. pose proof (u64_range (edenot E a1)) as Ha0. pose proof (u64_range (edenot E k)) as Hk0.
    unfold APS.uE in *.
    assert (AG1 : agree_on M M' (bv_unsigned (edenot E buf)) (bv_unsigned (edenot E len) + 64)).
    { intros y Hy. apply Hfp. apply (proj2 (in_fp_range2 E _ _ _ _ y)). left. rewrite uE_add_lit; lia. }
    assert (AG2 : agree_on M M' (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E n) * 4 + 12)).
    { intros y Hy. apply Hfp. apply (proj2 (in_fp_range2 E _ _ _ _ y)). right. rewrite uE_len4n12; lia. }
    repeat split; try assumption; try lia. exists bs, x, j, fq', fq. split; [rewrite <- Hin; apply input_frame; try lia; exact AG1|].
    split; [rewrite <- Hx; apply u32_at_frame; [lia|unfold two64 in *; lia|]; eapply agree_on_sub; [exact AG2|lia|lia]|].
    repeat split; assumption. }
  destruct (Nat.eqb id 62).
  { (* [comment removed for export] *) unfold p_acc, fp_acc in *.
    destruct args as [|a1 [|n [|len [|k [|t [|s [|tb [|sb [|? ?]]]]]]]]]; cbn [map] in *; try contradiction.
    destruct H as (Hn & Ha & Hk & Ht & Hs). pose proof (u64_range (edenot E a1)) as Ha0. pose proof (u64_range (edenot E k)) as Hk0. unfold APS.uE in *.
    assert (AG2 : agree_on M M' (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E n) * 4 + 12)).
    { intros x Hx. apply Hfp. apply (proj2 (in_fp_range1 E _ _ x)).
      rewrite uE_len4n12; lia. }
    assert (Hidx : idxm M' (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E n)) (bv_unsigned (edenot E len)) (bv_unsigned (edenot E k))
                 = idxm M (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E n)) (bv_unsigned (edenot E len)) (bv_unsigned (edenot E k))).
    { unfold idxm. destruct (Z.ltb_spec (bv_unsigned (edenot E k)) (bv_unsigned (edenot E n))); [|reflexivity].
      unfold u32v. rewrite (u32_at_frame M M'); [reflexivity|lia|unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG2|lia|lia]. }
    rewrite Hidx. repeat split; assumption. }
  destruct (Nat.eqb id 64).
  { (* [comment removed for export] *) unfold p_ocinv, fp_ocinv in *.
  destruct args as [|oc [|dd [|t [|? ?]]]]; cbn [map] in *; try contradiction.
  destruct H as (Hd & Ho & Hall). pose proof (u64_range (edenot E oc)) as Ho0. unfold APS.uE in *.
  assert (AG : agree_on M M' (bv_unsigned (edenot E oc)) (bv_unsigned (edenot E dd) * 8 + 4)).
  { intros x Hx. apply Hfp. apply (proj2 (in_fp_range1 E _ _ x)).
    rewrite uE_len8d4; lia. }
  split; [exact Hd|]. split; [exact Ho|]. intros d Hdd. destruct (Hall d Hdd) as (v & Hv & Hvt). exists v. split; [|exact Hvt].
  rewrite <- Hv. apply u32_at_frame; [lia|unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG|lia|lia]. }
  destruct (Nat.eqb id 65); [|contradiction].
  (* [comment removed for export] *) unfold p_iab, fp_iab in *.
  destruct args as [|ia [|dd [|? ?]]]; cbn [map] in *; try contradiction.
  destruct H as (Hd & Ho & Hall). pose proof (u64_range (edenot E ia)) as Hi0. unfold APS.uE in *.
  assert (AG : agree_on M M' (bv_unsigned (edenot E ia)) (bv_unsigned (edenot E dd) + 1)).
  { intros x Hx. apply Hfp. apply (proj2 (in_fp_range1 E _ _ x)).
    rewrite uE_add_lit; [lia | lia | unfold two64 in *; lia]. }
  split; [exact Hd|]. split; [exact Ho|]. intros d Hdd. destruct (Hall d Hdd) as (v & Hv & Hvt). exists v. split; [|exact Hvt].
  rewrite <- Hv. unfold u8_at. apply rdZ_frame; [lia|cbn [Z.of_nat]; unfold two64 in *; lia|]. eapply agree_on_sub; [exact AG|lia|cbn [Z.of_nat]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lhint : Type := list (nat * Z).

Fixpoint lin_subst_h (allkn : list kentry) (hs : lhint) (ts : list (Z * expr)) (lo hi : Z)
  : option (list (Z * expr) * Z * Z) :=
  match hs with
  | [] => Some (ts, lo, hi)
  | (i, q) :: r =>
      match nth_error allkn i with
      | Some (KRange e flo fhi) =>
          if fact_nowrap allkn e fhi then
            let c := fst (lin_of e) in let fts := snd (lin_of e) in
            let ts' := sub_fact q fts ts in
            if Z.leb 0 q then lin_subst_h allkn r ts' (lo + q * (flo - c)) (hi + q * (fhi - c))
            else lin_subst_h allkn r ts' (lo + q * (fhi - c)) (hi + q * (flo - c))
          else None
      | _ => None
      end
  end.

Definition lin_test_h (kn : list kentry) (hs : lhint) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_subst_h kn hs ts 0 0 with
  | Some (ts', lo0, hi0) =>
      match lin_range (erange kn) c ts' with
      | Some (lo, hi) => test (lo + lo0) (hi + hi0)
      | None => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Definition lin_ge0_h (kn : list kentry) (hs : lhint) (pos neg : xterms) : bool :=
  xt_nowrap kn pos && xt_nowrap kn neg &&
  lin_test_h kn hs (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo).

(* [comment removed for export] *)
Definition krange_h (kn : list kentry) (hs : lhint) (e : expr) (lo hi : Z) : bool :=
  lin_test_h kn hs (fst (lin_of e)) (snd (lin_of e))
    (fun l h => Z.leb lo l && Z.leb h hi && Z.leb 0 l && Z.ltb h two64).

(* [comment removed for export] *)
Definition shint : Type := Z * lhint.
Definition zscale (D : Z) (ts : list (Z * expr)) : list (Z * expr) := map (fun t => (D * fst t, snd t)) ts.
Definition zcdiv (a b : Z) : Z := - ((- a) / b).          (* [comment removed for export] *)
Definition lin_lo_h (kn : list kentry) (h : shint) (c : Z) (ts : list (Z * expr)) : option Z :=
  let (D, hs) := h in
  if Z.leb 1 D then
    match lin_subst_h kn hs (zscale D ts) 0 0 with
    | Some (ts', lo0, hi0) =>
        match lin_range (erange kn) (D * c) ts' with Some (lo, hi) => Some (zcdiv (lo + lo0) D) | None => None end
    | None => None
    end
  else None.
Definition lin_hi_h (kn : list kentry) (h : shint) (c : Z) (ts : list (Z * expr)) : option Z :=
  let (D, hs) := h in
  if Z.leb 1 D then
    match lin_subst_h kn hs (zscale D ts) 0 0 with
    | Some (ts', lo0, hi0) =>
        match lin_range (erange kn) (D * c) ts' with Some (lo, hi) => Some ((hi + hi0) / D) | None => None end
    | None => None
    end
  else None.
Definition krange_h2 (kn : list kentry) (hl hu : shint) (e : expr) (lo hi : Z) : bool :=
  match lin_lo_h kn hl (fst (lin_of e)) (snd (lin_of e)), lin_hi_h kn hu (fst (lin_of e)) (snd (lin_of e)) with
  | Some l, Some h => Z.leb lo l && Z.leb h hi && Z.leb 0 l && Z.ltb h two64
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition lin_ge0_h2 (kn : list kentry) (h : shint) (pos neg : xterms) : bool :=
  xt_nowrap kn pos && xt_nowrap kn neg &&
  match lin_lo_h kn h (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) with
  | Some l => Z.leb 0 l | None => false end.

Section LinSound.
Variable E : env.
Variable M : mem.

Lemma lin_subst_h_sound : forall kn, know_ok SEGS E M kn -> forall hs ts lo hi ts' lo' hi',
  lin_subst_h kn hs ts lo hi = Some (ts', lo', hi') ->
  forall v, tden E ts + lo <= v <= tden E ts + hi -> tden E ts' + lo' <= v <= tden E ts' + hi'.
Proof.
  intros kn Hkn hs. induction hs as [|[i q] r IH]; intros ts lo hi ts' lo' hi' H v Hv; cbn [lin_subst_h] in H.
  - injection H as <- <- <-. exact Hv.
  - destruct (nth_error kn i) as [K|] eqn:Hi; [|discriminate].
    destruct K as [| | | | |e flo fhi| | | |]; try discriminate.
    destruct (fact_nowrap kn e fhi) eqn:Hnw; [|discriminate].
    assert (HK : kentry_ok SEGS E M (KRange e flo fhi)).
    { apply (proj1 (Forall_forall _ _) Hkn). eapply nth_error_In. exact Hi. }
    cbn [kentry_ok] in HK.
    pose proof (fact_nowrap_sound SEGS E M kn e flo fhi Hkn Hnw HK) as He.
    pose proof (sub_fact_sound E q (snd (lin_of e)) ts) as Hs.
    destruct (Z.leb_spec 0 q).
    + apply (IH _ _ _ _ _ _ H). rewrite Hs. nia.
    + apply (IH _ _ _ _ _ _ H). rewrite Hs. nia.
Qed.

Lemma lin_test_h_sound : forall kn hs c ts test,
  know_ok SEGS E M kn -> lin_test_h kn hs c ts test = true ->
  exists lo hi, test lo hi = true /\ lo <= c + tden E ts <= hi.
Proof.
  intros kn hs c ts test Hkn H. unfold lin_test_h in H.
  destruct (lin_subst_h kn hs ts 0 0) as [[[ts' lo0] hi0]|] eqn:Hs; [|discriminate].
  destruct (lin_range (erange kn) c ts') as [[lo hi]|] eqn:Hlr; [|discriminate].
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound SEGS E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  pose proof (lin_subst_h_sound kn Hkn hs ts 0 0 ts' lo0 hi0 Hs (tden E ts) ltac:(lia)) as Hv.
  exists (lo + lo0), (hi + hi0). split; [exact H | lia].
Qed.

Lemma lin_ge0_h_sound : forall kn hs pos neg,
  know_ok SEGS E M kn -> lin_ge0_h kn hs pos neg = true -> xt_den E neg <= xt_den E pos.
Proof.
  intros kn hs pos neg Hkn H. unfold lin_ge0_h in H.
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [Hp Hn].
  pose proof (xt_lin_sound SEGS E M kn pos Hkn Hp) as XP. pose proof (xt_lin_sound SEGS E M kn neg Hkn Hn) as XN.
  apply (lin_test_h_sound kn) in Ht as (lo & hi & Ht & Hb); [|exact Hkn].
  apply Z.leb_le in Ht. rewrite lsub_e_sound in Hb. lia.
Qed.

Lemma zscale_sound : forall D ts, tden E (zscale D ts) = D * tden E ts.
Proof. intros D ts. unfold zscale. induction ts as [|[k a] r IH]; cbn [map tden fst snd]; [lia|]. rewrite IH. lia. Qed.
Lemma zcdiv_le : forall a D v, 0 < D -> a <= D * v -> zcdiv a D <= v.
Proof.
  intros a D v HD H. unfold zcdiv.
  assert (- v * D <= - a) by lia. pose proof (Z.div_le_lower_bound (-a) D (-v) HD ltac:(lia)). lia.
Qed.
Lemma zdiv_ge : forall a D v, 0 < D -> D * v <= a -> v <= a / D.
Proof. intros a D v HD H. apply Z.div_le_lower_bound; lia. Qed.
Lemma lin_lo_h_sound : forall kn h c ts l, know_ok SEGS E M kn -> lin_lo_h kn h c ts = Some l -> l <= c + tden E ts.
Proof.
  intros kn [D hs] c ts l Hkn H. unfold lin_lo_h in H. destruct (Z.leb_spec 1 D); [|discriminate].
  destruct (lin_subst_h kn hs (zscale D ts) 0 0) as [[[ts' lo0] hi0]|] eqn:Hs; [|discriminate].
  destruct (lin_range (erange kn) (D * c) ts') as [[lo hi]|] eqn:Hlr; [|discriminate]. injection H as <-.
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound SEGS E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  pose proof (lin_subst_h_sound kn Hkn hs (zscale D ts) 0 0 ts' lo0 hi0 Hs (tden E (zscale D ts)) ltac:(lia)) as Hv.
  rewrite zscale_sound in Hv. apply zcdiv_le; [lia|]. lia.
Qed.
Lemma lin_hi_h_sound : forall kn h c ts u, know_ok SEGS E M kn -> lin_hi_h kn h c ts = Some u -> c + tden E ts <= u.
Proof.
  intros kn [D hs] c ts u Hkn H. unfold lin_hi_h in H. destruct (Z.leb_spec 1 D); [|discriminate].
  destruct (lin_subst_h kn hs (zscale D ts) 0 0) as [[[ts' lo0] hi0]|] eqn:Hs; [|discriminate].
  destruct (lin_range (erange kn) (D * c) ts') as [[lo hi]|] eqn:Hlr; [|discriminate]. injection H as <-.
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound SEGS E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  pose proof (lin_subst_h_sound kn Hkn hs (zscale D ts) 0 0 ts' lo0 hi0 Hs (tden E (zscale D ts)) ltac:(lia)) as Hv.
  rewrite zscale_sound in Hv. apply zdiv_ge; [lia|]. lia.
Qed.
Lemma krange_h2_sound : forall kn hl hu e lo hi,
  know_ok SEGS E M kn -> krange_h2 kn hl hu e lo hi = true -> kentry_ok SEGS E M (KRange e lo hi).
Proof.
  intros kn hl hu e lo hi Hkn H. unfold krange_h2 in H.
  destruct (lin_lo_h kn hl (fst (lin_of e)) (snd (lin_of e))) as [l|] eqn:Hl; [|discriminate].
  destruct (lin_hi_h kn hu (fst (lin_of e)) (snd (lin_of e))) as [h|] eqn:Hh; [|discriminate].
  apply (lin_lo_h_sound kn) in Hl; [|exact Hkn]. apply (lin_hi_h_sound kn) in Hh; [|exact Hkn].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden in Hq. cbn [kentry_ok].
  pose proof (u64_range (edenot E e)) as Hr. unfold uE in Hq. unfold two64 in H4.
  assert (q = 0) by nia. subst q. lia.
Qed.
Lemma lin_ge0_h2_sound : forall kn h pos neg,
  know_ok SEGS E M kn -> lin_ge0_h2 kn h pos neg = true -> xt_den E neg <= xt_den E pos.
Proof.
  intros kn h pos neg Hkn H. unfold lin_ge0_h2 in H.
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [Hp Hn].
  pose proof (xt_lin_sound SEGS E M kn pos Hkn Hp) as XP. pose proof (xt_lin_sound SEGS E M kn neg Hkn Hn) as XN.
  destruct (lin_lo_h kn h _ _) as [l|] eqn:Hl; [|discriminate]. apply Z.leb_le in Ht.
  apply (lin_lo_h_sound kn) in Hl; [|exact Hkn]. rewrite lsub_e_sound in Hl. lia.
Qed.

Lemma krange_h_sound : forall kn hs e lo hi,
  know_ok SEGS E M kn -> krange_h kn hs e lo hi = true -> kentry_ok SEGS E M (KRange e lo hi).
Proof.
  intros kn hs e lo hi Hkn H. unfold krange_h in H.
  apply (lin_test_h_sound kn) in H as (l & h & Ht & Hb); [|exact Hkn].
  apply andb_prop in Ht as [Ht H4]. apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden in Hq. cbn [kentry_ok].
  pose proof (u64_range (edenot E e)) as Hr. unfold uE in Hq. unfold two64 in H4.
  assert (q = 0) by nia. subst q. lia.
Qed.
End LinSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition addr_is (kn : list kentry) (a : saddr) (e : xterms) : bool :=
  lin_ge0 kn [(a_base a, a_off a)] e && lin_ge0 kn e [(a_base a, a_off a)].

Lemma addr_is_sound : forall E M kn a e, know_ok SEGS E M kn -> addr_is kn a e = true -> estart E a = xt_den E e.
Proof.
  intros E M kn a e Hkn H. unfold addr_is in H. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H1) as A. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H2) as B.
  cbn [xt_den] in A, B. unfold estart. lia.
Qed.

(* [comment removed for export] *)
Fixpoint find_rec (kn allkn : list kentry) (e : xterms) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord a w' v :: rest => if (Nat.eqb w' w && addr_is allkn a e)%bool then Some v else find_rec rest allkn e w
  | _ :: rest => find_rec rest allkn e w
  end.

Lemma find_rec_sound : forall E M allkn kn e w v, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_rec kn allkn e w = Some v ->
  (w <= 8)%nat /\ 0 <= xt_den E e /\ xt_den E e + Z.of_nat w <= 2 ^ 64 /\
  rdn SEGS M (Z_to_bv 64 (xt_den E e)) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M allkn kn e w v Hall Hkn. induction kn as [|K rest IH]; cbn [find_rec]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [a w' v'| | | | | | | | |]; try exact (IH Hrest H).
  destruct (Nat.eqb w' w && addr_is allkn a e)%bool eqn:Hb; [|exact (IH Hrest H)].
  injection H as <-. apply andb_prop in Hb as [Hw Ha]. apply Nat.eqb_eq in Hw. subst w'.
  cbn [kentry_ok] in HK. destruct HK as (Hw8 & Hfl & Hrd).
  pose proof (addr_is_sound E M allkn a e Hall Ha) as He. pose proof (flat_u E a _ Hfl) as Hu.
  destruct Hfl as (F1 & F2 & F3 & F4).
  split; [exact Hw8|]. split; [lia|]. split; [lia|].
  rewrite <- He. replace (Z_to_bv 64 (estart E a)) with (adenot E a); [exact Hrd|].
  apply bv_eq. rewrite Hu, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma rdZ_of_rec : forall E M allkn kn e w v, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_rec kn allkn e w = Some v -> rdZ M (xt_den E e) w = Some (bv_unsigned (edenot E v) mod 2 ^ (8 * Z.of_nat w)).
Proof.
  intros E M allkn kn e w v Hall Hkn H. destruct (find_rec_sound E M allkn kn e w v Hall Hkn H) as (_ & _ & _ & Hr).
  unfold rdZ. rewrite Hr, bytes_le_N. reflexivity.
Qed.

(* [comment removed for export] *)
Definition recval (w : nat) (v : expr) : expr := if Nat.eqb w 8 then v else EExt false 0 w v.
Lemma recval_sound : forall E w v, (1 <= w <= 8)%nat ->
  bv_unsigned (edenot E (recval w v)) = bv_unsigned (edenot E v) mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros E w v Hw. unfold recval. destruct (Nat.eqb_spec w 8) as [->|Hne].
  - symmetry. apply Z.mod_small. pose proof (u64_range (edenot E v)). cbn. lia.
  - cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul Z.pow_pos]. rewrite Z.div_1_r, u_lit64a.
    pose proof (u64_range (edenot E v)) as Hr.
    assert (Hm : 0 < 2 ^ (8 * Z.of_nat w) <= 2 ^ 64).
    { split; [apply Z.pow_pos_nonneg; lia|]. apply Z.pow_le_mono_r; lia. }
    apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E v)) (2 ^ (8 * Z.of_nat w)) ltac:(lia)). lia.
Qed.

Lemma recval4 : forall E v, bv_unsigned (edenot E (recval 4 v)) = bv_unsigned (edenot E v) mod 2 ^ 32.
Proof. intros. exact (recval_sound E 4 v ltac:(lia)). Qed.
Lemma recval1 : forall E v, bv_unsigned (edenot E (recval 1 v)) = bv_unsigned (edenot E v) mod 2 ^ 8.
Proof. intros. exact (recval_sound E 1 v ltac:(lia)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eSUB (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition eADDk (a : expr) (k : Z) : expr := mkAlu ALU_ADD a (ELit k).
Definition eMULk (k : Z) (a : expr) : expr := mkMd M_MUL (ELit k) a.

Lemma u_eSUB : forall E a b, uD E (eSUB a b) = (uD E a - uD E b) mod 2 ^ 64.
Proof. intros. unfold eSUB. rewrite mkAlu_denot. apply u_sub64. Qed.
Lemma u_eADDk : forall E a k, uD E (eADDk a k) = (uD E a + k) mod 2 ^ 64.
Proof. intros. unfold eADDk. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64a, Zplus_mod_idemp_r. reflexivity. Qed.
Lemma u_eMULk : forall E k a, uD E (eMULk k a) = (k * uD E a) mod 2 ^ 64.
Proof. intros. unfold eMULk. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64a, Zmult_mod_idemp_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma krange_of_modeq : forall E M e z lo hi,
  uD E e = z mod 2 ^ 64 -> 0 <= lo -> lo <= z <= hi -> hi < 2 ^ 64 -> kentry_ok SEGS E M (KRange e lo hi).
Proof. intros E M e z lo hi He Hlo Hz Hhi. cbn [kentry_ok]. rewrite He, Z.mod_small by lia. lia. Qed.

Definition hiZ (kn : list kentry) (e : expr) : Z :=
  Z.min (match xhi kn e with Some h => h | None => two64 - 1 end) (two64 - 1).
Lemma hiZ_sound : forall E M kn e, know_ok SEGS E M kn -> uD E e <= hiZ kn e < 2 ^ 64.
Proof.
  intros E M kn e Hkn. unfold hiZ, two64. pose proof (u64_range (edenot E e)) as R. destruct (xhi kn e) as [h|] eqn:H; [|lia].
  pose proof (xhi_sound SEGS E M kn e h Hkn H). lia.
Qed.

(* [comment removed for export] *)
Definition is_s1ok_for (len a1 n : expr) (g : gatom) : bool :=
  Nat.eqb (g_id g) 60 &&
  match g_args g with [b; l; a; m] => expr_eqb l len && expr_eqb a a1 && expr_eqb m n | _ => false end.
Definition has_s1ok (hyps : list gatom) (len a1 n : expr) : bool := existsb (is_s1ok_for len a1 n) hyps.

(* [comment removed for export] *)
Definition xN (n : nat) (e : expr) : xterms := repeat (e, 0) n.
Lemma xt_den_xN : forall E n e, xt_den E (xN n e) = Z.of_nat n * bv_unsigned (edenot E e).
Proof. intros E n e. unfold xN. induction n as [|n IH]; [reflexivity|]. cbn [repeat xt_den]. rewrite IH. lia. Qed.
Lemma xt_den_app : forall E a b, xt_den E (a ++ b) = xt_den E a + xt_den E b.
Proof. intros E a b. induction a as [|[e k] r IH]; cbn [xt_den app]; [lia|]. rewrite IH. lia. Qed.
(* [comment removed for export] *)
Definition addr_idx (a1 k : expr) : xterms := (a1, 0) :: xN 4 k.
Definition addr_idx1 (a1 k : expr) : xterms := (a1, 4) :: xN 4 k.      (* [comment removed for export] *)

Definition ltwo64 (z : Z) : bool := Z.ltb z two64.

(* [comment removed for export] *)
Definition KTriv : kentry := KRange (ELit 0) 0 0.
Definition derived1 (kn : list kentry) (hyps : list gatom) (g : gatom) : list kentry :=
  let id := g_id g in
  if Nat.eqb id 60 then
    match g_args g with
    | [buf; len; a1; n] => [KRange (eSUB len n) 0 (hiZ kn len)]
    | _ => [KTriv] end
  else if Nat.eqb id 61 then
    match g_args g with
    | [buf; len; a1; n; k; p] => [KRange (eSUB len p) 1 (hiZ kn len)]
    | _ => [KTriv] end
  else if Nat.eqb id 62 then
    match g_args g with
    | [a1; n; len; k; t; s; tbe; sbe] =>
      match tbe, sbe with
      | ELit tb, ELit sb =>
      let lh := hiZ kn len in let nh := hiZ kn n in
      if (has_s1ok hyps len a1 n && Z.leb 0 tb && Z.leb tb 2 && Z.leb 0 sb && Z.ltb sb 64
          && ltwo64 (5 * lh + 70) && ltwo64 (nh + 2))%bool then
        [KRange (eSUB (eADDk len (2 - tb)) t) 0 (lh + 2);
         KRange (eSUB (eADDk (eMULk 5 len) sb) (eMULk 3 s)) 0 (5 * lh + sb);
         KRange (eSUB (eADDk n 1) k) 0 (nh + 1)]
        ++ match find_rec kn kn (addr_idx a1 k) 4 with
           | Some v => let x := recval 4 v in
               [KRange (eSUB (eADDk x (2 - tb)) t) 0 (lh + 2);
                KRange (eSUB (eADDk (eMULk 5 x) sb) (eMULk 3 s)) 0 (5 * lh + sb);
                KRange (eSUB len x) 0 lh]
           | None => [KTriv; KTriv; KTriv]
           end
      else [KTriv; KTriv; KTriv; KTriv; KTriv; KTriv]
      | _, _ => [KTriv; KTriv; KTriv; KTriv; KTriv; KTriv] end
    | _ => [KTriv; KTriv; KTriv; KTriv; KTriv; KTriv] end
  else [].
(* [comment removed for export] *)
Definition derived_k1 (kn : list kentry) (K : kentry) : kentry :=
  match K with
  | KRange (EAlu ALU_SLTU a b) lo hi =>
      if (Z.eqb lo 0 && Z.eqb hi 0)%bool then KRange (eSUB a b) 0 (hiZ kn a)
      else if (Z.eqb lo 1 && Z.eqb hi 1)%bool then KRange (eSUB b a) 1 (hiZ kn b)
      else KTriv
  | _ => KTriv
  end.
Definition derived (kn : list kentry) (hyps : list gatom) : list kentry :=
  map (derived_k1 kn) kn ++ flat_map (derived1 kn hyps) hyps.

(* [comment removed for export] *)
Section DerivedSound.
Variable E : env.
Variable M : mem.

Lemma nthb_range : forall bs i, (forall x, In x bs -> 0 <= x <= 255) -> 0 <= nthb bs i <= 255.
Proof.
  intros bs i H. unfold nthb. destruct (i <? 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [Hl|Hg].
  - apply H. apply nth_In. exact Hl.
  - rewrite nth_overflow by exact Hg. lia.
Qed.
Lemma input_bytes_range : forall buf len bs, input M buf len = Some bs -> forall x, In x bs -> 0 <= x <= 255.
Proof.
  intros buf len bs H x Hx. unfold input in H. destruct (rdn SEGS M (Z_to_bv 64 buf) (Z.to_nat (len + 64))) as [bb|]; [|discriminate].
  injection H as <-. apply in_map_iff in Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as Hr.
  change (bv_modulus 8) with 256%Z in Hr. lia.
Qed.

Lemma s1ok_idxm_le_len : forall buf len a1 n k, p_s1ok [buf; len; a1; n] M -> 0 <= k -> idxm M a1 n len k <= len.
Proof.
  intros buf len a1 n k H Hk. unfold p_s1ok in H.
  destruct H as (Hl & _ & _ & Hn & bs & Hin & Hs & Hlen & _ & Hidx & _).
  unfold idxm. destruct (Z.ltb_spec k n) as [Hlt|]; [|lia].
  unfold u32v. rewrite <- (Z2Nat.id k) by lia.
  assert (Hkn : (Z.to_nat k < length (fst (S1M.result (nthb bs) len)))%nat) by lia.
  rewrite (Hidx (Z.to_nat k) Hkn).
  pose proof (S1M.indexes_lt_len (nthb bs) len (nth (Z.to_nat k) (fst (S1M.result (nthb bs) len)) 0) (nth_In _ _ Hkn)). lia.
Qed.

Lemma s1ok_rec_idxm : forall buf len a1 n k x, p_s1ok [buf; len; a1; n] M -> 0 <= k <= n + 1 ->
  u32_at M (a1 + 4 * k) = Some x -> idxm M a1 n len k = x.
Proof.
  intros buf len a1 n k x H Hk Hx. unfold p_s1ok in H.
  destruct H as (Hl & _ & _ & Hn & bs & Hin & Hs & Hlen & _ & Hidx & Hs0 & Hs1 & _).
  unfold idxm, u32v. destruct (Z.ltb_spec k n) as [Hlt|Hge]; [rewrite Hx; reflexivity|].
  assert (k = n \/ k = n + 1) as [->| ->] by lia.
  - rewrite Hs0 in Hx. injection Hx as ->. reflexivity.
  - replace (a1 + 4 * (n + 1)) with (a1 + 4 * n + 4) in Hx by lia. rewrite Hs1 in Hx. injection Hx as ->. reflexivity.
Qed.

Lemma s1ok_n_le_len : forall buf len a1 n, p_s1ok [buf; len; a1; n] M -> 1 <= n <= len.
Proof.
  intros buf len a1 n H. unfold p_s1ok in H. destruct H as (Hl & _ & _ & Hn & bs & Hin & Hs & Hlen & _).
  pose proof (S1M.n_le_len (nthb bs) len Hl). lia.
Qed.

Lemma has_s1ok_sound : forall hyps len a1 n, Forall (APS.gholds GP2 E M) hyps -> has_s1ok hyps len a1 n = true ->
  exists buf, p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M.
Proof.
  intros hyps len a1 n Hh H. unfold has_s1ok in H. apply existsb_exists in H as (g & Hg & Hb).
  unfold is_s1ok_for in Hb. apply andb_prop in Hb as [Hid Hb]. apply Nat.eqb_eq in Hid.
  destruct g as [id args]. cbn [g_id g_args] in Hid, Hb. subst id.
  destruct args as [|b [|l [|a [|m [|? ?]]]]]; try discriminate.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. subst.
  pose proof (proj1 (Forall_forall _ _) Hh _ Hg) as G. unfold APS.gholds, GP2 in G. cbn [g_id g_args map Nat.eqb] in G.
  exists b. exact G.
Qed.

Lemma mod_small_iff : forall z, 0 <= z < 2 ^ 64 -> z mod 2 ^ 64 = z.
Proof. intros. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma fact_sub : forall A B za zb lo hi,
  uD E A = za mod 2 ^ 64 -> uD E B = zb mod 2 ^ 64 -> 0 <= lo -> lo <= za - zb <= hi -> hi < 2 ^ 64 ->
  kentry_ok SEGS E M (KRange (eSUB A B) lo hi).
Proof.
  intros A B za zb lo hi HA HB Hlo Hz Hhi. apply (krange_of_modeq E M _ (za - zb)); try lia.
  rewrite u_eSUB, HA, HB. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma u_mod_self : forall e, uD E e = uD E e mod 2 ^ 64.
Proof. intros. symmetry. apply Z.mod_small. apply u64_range. Qed.
Lemma u_eADDk_z : forall a k za, uD E a = za mod 2 ^ 64 -> uD E (eADDk a k) = (za + k) mod 2 ^ 64.
Proof. intros a k za H. rewrite u_eADDk, H. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma u_eMULk_z : forall k a za, uD E a = za mod 2 ^ 64 -> uD E (eMULk k a) = (k * za) mod 2 ^ 64.
Proof. intros k a za H. rewrite u_eMULk, H. rewrite Zmult_mod_idemp_r. reflexivity. Qed.

Lemma KTriv_ok : kentry_ok SEGS E M KTriv.
Proof. unfold KTriv. cbn [kentry_ok edenot]. rewrite u_lit64a. rewrite Z.mod_0_l by lia. lia. Qed.
Lemma KTrivs_ok : forall n, know_ok SEGS E M (repeat KTriv n).
Proof. intros n. induction n; cbn [repeat]; constructor; [apply KTriv_ok | exact IHn]. Qed.
Lemma derived1_sound : forall kn hyps g, know_ok SEGS E M kn -> Forall (APS.gholds GP2 E M) hyps ->
  APS.gholds GP2 E M g -> know_ok SEGS E M (derived1 kn hyps g).
Proof.
  intros kn hyps [id args] Hkn Hh Hg. unfold derived1. cbn [g_id g_args].
  pose proof (KTrivs_ok 1) as T1. pose proof (KTrivs_ok 3) as T3. pose proof (KTrivs_ok 6) as T6. cbn [repeat] in T1, T3, T6.
  unfold APS.gholds, GP2 in Hg. cbn [g_id g_args] in Hg.
  pose proof (fun e => hiZ_sound E M kn e Hkn) as HI. unfold APS.uE in *.
  destruct (Nat.eqb id 60).
  { destruct args as [|buf [|len [|a1 [|n [|? ?]]]]]; try exact T1.
    cbn [map] in Hg. pose proof (s1ok_n_le_len _ _ _ _ Hg) as Hn.
    pose proof (HI len). pose proof (u64_range (edenot E n)).
    constructor; [|constructor]. apply (fact_sub len n (uD E len) (uD E n)); try apply u_mod_self; lia. }
  destruct (Nat.eqb id 61).
  { destruct args as [|buf [|len [|a1 [|n [|k [|p [|? ?]]]]]]]; try exact T1.
    cbn [map] in Hg. unfold p_str in Hg. destruct Hg as (Hl & Hb & _ & _ & bs & x & j & fq' & fq & _ & _ & _ & _ & Hpj & Hjl & _).
    pose proof (HI len). pose proof (u64_range (edenot E p)).
    constructor; [|constructor]. apply (fact_sub len p (uD E len) (uD E p)); try apply u_mod_self; lia. }
  destruct (Nat.eqb id 62); [|apply Forall_nil].
  destruct args as [|a1 [|n [|len [|k [|t [|s' [|tb [|sb [|? ?]]]]]]]]]; try exact T6.
  destruct tb as [tb| | | | | | |]; cbv beta iota zeta; try exact T6.
  destruct sb as [sb| | | | | | |]; cbv beta iota zeta; try exact T6.
  match goal with |- know_ok _ _ _ (if ?c then _ else _) => destruct c eqn:Hc; [|exact T6] end.
  repeat (apply andb_prop in Hc as [Hc ?H]). rename Hc into Hs1.
  apply Z.leb_le in H4. apply Z.leb_le in H3. apply Z.leb_le in H2. apply Z.ltb_lt in H1.
  unfold ltwo64, two64 in H0, H. apply Z.ltb_lt in H0. apply Z.ltb_lt in H.
  cbn [map] in Hg. unfold p_acc in Hg. cbn [edenot] in Hg. rewrite !u_lit64a in Hg.
  rewrite (Z.mod_small tb) in Hg by lia. rewrite (Z.mod_small sb) in Hg by lia.
  destruct Hg as (Hn0 & Ha1 & Hk & Ht & Hs).
  destruct (has_s1ok_sound hyps len a1 n Hh Hs1) as [buf S1].
  pose proof (s1ok_idxm_le_len _ _ _ _ (uD E k) S1 (proj1 (u64_range _))) as Hil.
  pose proof (s1ok_n_le_len _ _ _ _ S1) as Hnl.
  pose proof (HI len) as HL. pose proof (HI n) as HN.
  pose proof (u64_range (edenot E len)) as RL. pose proof (u64_range (edenot E t)) as RT. pose proof (u64_range (edenot E s')) as RS.
  pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E n)) as RN. pose proof (u64_range (edenot E a1)) as RA.
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (_ & Hbl & _).
  set (I := idxm M (uD E a1) (uD E n) (uD E len) (uD E k)) in *.
  apply Forall_app. split.
  { constructor; [|constructor; [|constructor; [|apply Forall_nil]]].
    - apply (fact_sub _ _ (uD E len + (2 - tb)) (uD E t)); [apply u_eADDk_z; apply u_mod_self | apply u_mod_self | lia | lia | lia].
    - apply (fact_sub _ _ (5 * uD E len + sb) (3 * uD E s')).
      + apply u_eADDk_z. apply u_eMULk_z. apply u_mod_self.
      + apply u_eMULk_z. apply u_mod_self.
      + lia. + lia. + lia.
    - apply (fact_sub _ _ (uD E n + 1) (uD E k)); [apply u_eADDk_z; apply u_mod_self | apply u_mod_self | lia | lia | lia]. }
  destruct (find_rec kn kn (addr_idx a1 k) 4) as [v|] eqn:Hr; [|exact T3].
  pose proof (rdZ_of_rec E M kn kn _ _ _ Hkn Hkn Hr) as Hrd.
  assert (Had : xt_den E (addr_idx a1 k) = uD E a1 + 4 * uD E k).
  { unfold addr_idx. cbn [xt_den]. rewrite xt_den_xN. lia. }
  rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * uD E k) 4) with (u32_at M (uD E a1 + 4 * uD E k)) in Hrd.
  assert (Hk2 : 0 <= bv_unsigned (edenot E k) <= bv_unsigned (edenot E n) + 1) by lia.
  pose proof (s1ok_rec_idxm _ _ _ _ _ _ S1 Hk2 Hrd) as HI2. fold I in HI2.
  pose proof (recval_sound E 4 v ltac:(lia)) as Hx. cbn [Z.of_nat Z.mul Pos.mul] in Hx, HI2.
  set (x := uD E (recval 4 v)) in *.
  assert (HxI : I = x) by (rewrite HI2; symmetry; exact Hx).
  pose proof (u64_range (edenot E (recval 4 v))) as RX. fold x in RX. change (bv_unsigned (edenot E (recval 4 v))) with x in RX.
  constructor; [|constructor; [|constructor; [|apply Forall_nil]]].
  - apply (fact_sub _ _ (x + (2 - tb)) (uD E t)); [apply u_eADDk_z; apply u_mod_self | apply u_mod_self | lia | lia | lia].
  - apply (fact_sub _ _ (5 * x + sb) (3 * uD E s')).
    + apply u_eADDk_z. apply u_eMULk_z. apply u_mod_self.
    + apply u_eMULk_z. apply u_mod_self.
    + lia. + lia. + lia.
  - apply (fact_sub _ _ (uD E len) x); [apply u_mod_self | apply u_mod_self | lia | lia | lia].
Qed.

Lemma derived_k1_sound : forall kn K, know_ok SEGS E M kn -> kentry_ok SEGS E M K -> kentry_ok SEGS E M (derived_k1 kn K).
Proof.
  intros kn K Hkn HK. pose proof KTriv_ok as T. unfold derived_k1.
  destruct K as [| | | | |e lo hi| | | |]; try exact T. destruct e as [| |op a b| | | | |]; try exact T. destruct op; try exact T.
  cbn [kentry_ok edenot] in HK. rewrite u_sltu64 in HK.
  pose proof (hiZ_sound E M kn a Hkn) as Ha. pose proof (hiZ_sound E M kn b Hkn) as Hb.
  pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
  destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:H0.
  - apply andb_prop in H0 as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
    destruct (Z.ltb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))); [lia|].
    apply (fact_sub a b (uD E a) (uD E b)); try apply u_mod_self; lia.
  - destruct (Z.eqb lo 1 && Z.eqb hi 1)%bool eqn:H1; [|exact T].
    apply andb_prop in H1 as [H2 H3]. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
    destruct (Z.ltb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))); [|lia].
    apply (fact_sub b a (uD E b) (uD E a)); try apply u_mod_self; lia.
Qed.
Lemma derived_sound : forall kn hyps, know_ok SEGS E M kn -> Forall (APS.gholds GP2 E M) hyps ->
  know_ok SEGS E M (derived kn hyps).
Proof.
  intros kn hyps Hkn Hh. unfold derived. apply Forall_app. split.
  - apply Forall_map. apply Forall_forall. intros K HK. apply derived_k1_sound; [exact Hkn | exact (proj1 (Forall_forall _ _) Hkn K HK)].
  - apply Forall_flat_map. apply Forall_forall. intros g Hg.
    apply derived1_sound; [exact Hkn | exact Hh | exact (proj1 (Forall_forall _ _) Hh g Hg)].
Qed.
End DerivedSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AtomLemmas.
Variable E : env.
Variable M : mem.

Lemma Z_to_bv_plus_nat : forall a d, 0 <= a -> 0 <= d -> Z_to_bv 64 (a + d) = (Z_to_bv 64 a + nat_to_word (Z.to_nat d))%bv.
Proof.
  intros a d Ha Hd. unfold nat_to_word. rewrite Z2Nat.id by lia. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zplus_mod. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn : forall (l : list byte) d, (d < length l)%nat -> firstn 1 (skipn d l) = [nth d l (Z_to_bv 8 0)].
Proof.
  intros l d Hd. destruct (skipn d l) as [|y ys] eqn:Hsk.
  - exfalso. apply (f_equal (@length _)) in Hsk. rewrite length_skipn in Hsk. cbn in Hsk. lia.
  - cbn. f_equal. pose proof (nth_skipn d l 0 (Z_to_bv 8 0)) as Hn. rewrite Hsk, Nat.add_0_r in Hn. cbn in Hn. exact Hn.
Qed.
Lemma nthb_map : forall (bb : list byte) d, 0 <= d -> (Z.to_nat d < length bb)%nat ->
  nthb (map bv_unsigned bb) d = bv_unsigned (nth (Z.to_nat d) bb (Z_to_bv 8 0)).
Proof.
  intros bb d Hd Hlt. unfold nthb. destruct (Z.ltb_spec d 0); [lia|].
  rewrite <- (map_nth bv_unsigned). reflexivity.
Qed.
Lemma input_byte : forall buf len bs kn a bv,
  0 <= buf -> buf + len + 64 < two64 -> 0 <= len -> input M buf len = Some bs -> know_ok SEGS E M kn ->
  find_rec kn kn a 1 = Some bv -> 0 <= xt_den E a - buf < len + 64 ->
  nthb bs (xt_den E a - buf) = uD E (recval 1 bv).
Proof.
  intros buf len bs kn a bv Hb Hbl Hl Hin Hkn Hr Hx.
  destruct (find_rec_sound E M kn kn a 1 bv Hkn Hkn Hr) as (_ & Hge & Hle & Hrd).
  unfold input in Hin. destruct (rdn SEGS M (Z_to_bv 64 buf) (Z.to_nat (len + 64))) as [bb|] eqn:Hall; [|discriminate].
  injection Hin as <-.
  pose proof (rdn_length _ _ _ _ _ Hall) as Hlen.
  set (d := xt_den E a - buf) in *.
  pose proof (rdn_slice SEGS M (Z.to_nat (len + 64)) (Z_to_bv 64 buf) bb (Z.to_nat d) 1 Hall ltac:(lia)) as Hs.
  rewrite <- Z_to_bv_plus_nat in Hs by lia. replace (buf + d) with (xt_den E a) in Hs by lia.
  rewrite Hrd in Hs. rewrite firstn1_skipn in Hs by lia. injection Hs as Hb1.
  rewrite nthb_map by lia. rewrite <- Hb1. rewrite recval_sound by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ (8 * Z.of_nat 1)). reflexivity.
Qed.

Lemma qsearch_det : forall b f1 f2 i j1 j2, S1M.qsearch b f1 i = Some j1 -> S1M.qsearch b f2 i = Some j2 -> j1 = j2.
Proof.
  intros b f1 f2 i j1 j2 H1 H2.
  pose proof (S1M.qsearch_mono_fuel b f1 (Nat.max f1 f2) i j1 H1 ltac:(lia)) as A.
  pose proof (S1M.qsearch_mono_fuel b f2 (Nat.max f1 f2) i j2 H2 ltac:(lia)) as B. rewrite A in B. injection B as ->. reflexivity.
Qed.
Lemma qsearch_at_quote : forall b f p j, S1M.qsearch b f p = Some j -> b p = S1M.QUOTE -> j = p.
Proof.
  intros b f p j H Hq. destruct f as [|f]; cbn [S1M.qsearch] in H; [discriminate|].
  rewrite Hq in H. cbn in H. injection H as <-. reflexivity.
Qed.

Section WithS1.
Variables buf len a1 n : Z.
Variable bs : list Z.
Hypothesis S1 : p_s1ok [buf; len; a1; n] M.
Hypothesis Hbs : input M buf len = Some bs.

Lemma s1_facts : 0 <= len /\ buf + len + 64 < two64 /\ a1 + 4 * n + 12 < two64 /\ 1 <= n /\
  snd (S1M.result (nthb bs) len) = S1M.SUCCESS /\ Z.of_nat (length (fst (S1M.result (nthb bs) len))) = n /\ nthb bs len = 0 /\
  (forall k, (k < length (fst (S1M.result (nthb bs) len)))%nat -> u32_at M (a1 + 4 * Z.of_nat k) = Some (nth k (fst (S1M.result (nthb bs) len)) 0)) /\
  u32_at M (a1 + 4 * n) = Some len /\ u32_at M (a1 + 4 * n + 4) = Some len /\ u32_at M (a1 + 4 * n + 8) = Some 0.
Proof.
  pose proof S1 as H. unfold p_s1ok in H. destruct H as (A & B & C & D & bs' & Hin & rest).
  rewrite Hbs in Hin. injection Hin as <-. repeat (split; [tauto|]); tauto.
Qed.
Lemma bytes_range : forall k, 0 <= k -> 0 <= nthb bs k <= 255.
Proof. intros k _. apply nthb_range. intros x Hx. eapply (input_bytes_range M); [exact Hbs | exact Hx]. Qed.

Lemma idxm_lt : forall k, 0 <= k < n -> idxm M a1 n len k = nth (Z.to_nat k) (fst (S1M.result (nthb bs) len)) 0 /\ 0 <= nth (Z.to_nat k) (fst (S1M.result (nthb bs) len)) 0 < len.
Proof.
  intros k Hk. destruct s1_facts as (_ & _ & _ & _ & _ & Hlen & _ & Hidx & _).
  assert (Hkn : (Z.to_nat k < length (fst (S1M.result (nthb bs) len)))%nat) by lia.
  unfold idxm. destruct (Z.ltb_spec k n); [|lia]. unfold u32v.
  rewrite <- (Z2Nat.id k) at 1 by lia. rewrite (Hidx _ Hkn). split; [reflexivity|].
  exact (S1M.indexes_lt_len (nthb bs) len _ (nth_In _ 0 Hkn)).
Qed.
Lemma idxm_ge : forall k, n <= k -> idxm M a1 n len k = len.
Proof. intros k Hk. unfold idxm. destruct (Z.ltb_spec k n); [lia|reflexivity]. Qed.
Lemma idxm_le_len : forall k, 0 <= k -> idxm M a1 n len k <= len.
Proof. intros k Hk. destruct (Z.lt_ge_cases k n). - destruct (idxm_lt k ltac:(lia)); lia. - rewrite idxm_ge; lia. Qed.

Lemma idxm_ge_k : forall k, 0 <= k <= n -> k <= idxm M a1 n len k.
Proof.
  intros k Hk. destruct s1_facts as (Hl & _ & _ & _ & _ & Hlen & _).
  destruct (Z.lt_ge_cases k n) as [Hlt|Hge].
  - destruct (idxm_lt k ltac:(lia)) as [-> _].
    pose proof (S1M.sorted_lt_nth_ge (fst (S1M.result (nthb bs) len)) (S1M.indexes_sorted _ _)
                  ltac:(intros x Hx; destruct (S1M.indexes_lt_len (nthb bs) len x Hx); lia) (Z.to_nat k) ltac:(lia)). lia.
  - rewrite idxm_ge by lia. pose proof (S1M.n_le_len (nthb bs) len Hl). lia.
Qed.
Lemma idxm_step : forall k, 0 <= k < n -> idxm M a1 n len k + 1 <= idxm M a1 n len (k + 1).
Proof.
  intros k Hk. destruct s1_facts as (Hl & _ & _ & _ & _ & Hlen & _).
  destruct (idxm_lt k Hk) as [E1 B1].
  destruct (Z.lt_ge_cases (k + 1) n) as [Hlt|Hge].
  - destruct (idxm_lt (k + 1) ltac:(lia)) as [E2 _]. rewrite E1, E2.
    pose proof (S1M.indexes_sorted (nthb bs) len (Z.to_nat k) (Z.to_nat (k + 1)) ltac:(lia) ltac:(lia)). lia.
  - rewrite (idxm_ge (k + 1)) by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma idxm_of_rec : forall k x, 0 <= k <= n + 1 -> u32_at M (a1 + 4 * k) = Some x -> idxm M a1 n len k = x.
Proof. intros k x Hk Hx. eapply s1ok_rec_idxm; [exact S1 | exact Hk | exact Hx]. Qed.
(* [comment removed for export] *)
Lemma lt_n_of_byte : forall k, 0 <= k <= n + 1 -> nthb bs (idxm M a1 n len k) <> 0 -> k < n.
Proof.
  intros k Hk Hb. destruct s1_facts as (_ & _ & _ & _ & _ & _ & Hz & _).
  destruct (Z.lt_ge_cases k n); [assumption|]. rewrite idxm_ge in Hb by lia. congruence.
Qed.
(* [comment removed for export] *)
Lemma idxm_string : forall k, 0 <= k < n -> nthb bs (idxm M a1 n len k) = 34 ->
  exists j fq, idxm M a1 n len k < j /\ j < len /\ S1M.qsearch (nthb bs) fq (idxm M a1 n len k + 1) = Some j /\
               j + 1 <= idxm M a1 n len (k + 1).
Proof.
  intros k Hk Hq. destruct s1_facts as (Hl & _ & _ & _ & Hsucc & Hlen & _).
  destruct (idxm_lt k Hk) as [E1 B1].
  destruct (S1M.string_next (nthb bs) len bytes_range Hsucc (Z.to_nat k) ltac:(lia) ltac:(rewrite <- E1; exact Hq))
    as (j & fq & A & B & C & D).
  exists j, fq. rewrite E1. split; [lia|]. split; [lia|]. split; [exact C|].
  destruct (Z.lt_ge_cases (k + 1) n) as [Hlt|Hge].
  - destruct (idxm_lt (k + 1) ltac:(lia)) as [E2 _]. rewrite E2.
    replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. specialize (D ltac:(lia)). lia.
  - rewrite (idxm_ge (k + 1)) by lia. lia.
Qed.
End WithS1.
End AtomLemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive extra : Type :=
| XIdx (k : expr) (h : shint)               (* [comment removed for export] *)
| XStr (k : expr) (h : shint)               (* [comment removed for export] *)
| XSltu (i : nat) (hal hau hbl hbu : shint) (* [comment removed for export] *)
| XStrStep (i : nat) (d : Z)               (* [comment removed for export] *)
| XUHex (i : nat) (segs : list (nat * list Z))  (* [comment removed for export] *)
| XStep (k : expr) (h : shint)              (* [comment removed for export] *)
| XOc (i : nat) (d' : expr) (h : shint)         (* [comment removed for export] *)
| XExtEq (n : nat) (e : expr) (hl hu : shint)   (* [comment removed for export] *)
| XIab (i : nat) (d' : expr) (hl hu : shint)    (* [comment removed for export] *)
.
(* [comment removed for export] *)
Inductive kmode : Type :=
| KSame                                     (* [comment removed for export] *)
| KSameRel                                  (* [comment removed for export] *)
| KAdvNZ                                    (* [comment removed for export] *)
| KAdvStr                                   (* [comment removed for export] *)
| KStrEnd (istr : nat)                      (* [comment removed for export] *)
| KAdv2NZ                                   (* [comment removed for export] *)
| KAdv2Str                                  (* [comment removed for export] *)
| KAdvN (n : nat) (str : bool)              (* [comment removed for export] *)
.
Inductive rule : Type :=
| RNone                                     (* [comment removed for export] *)
| RHyp (i : nat)                            (* [comment removed for export] *)
| RLin (xs : list extra) (hl hu : shint)   (* [comment removed for export] *)
| RAccInit (hk ht hs : shint)               (* [comment removed for export] *)
| RAcc (i : nat) (m : kmode) (hT hS : shint)   (* [comment removed for export] *)
| RStrStart (hk : shint)                    (* [comment removed for export] *)
| RStr (i : nat) (d : Z)                    (* [comment removed for export] *)
| ROc (src : option nat) (recs : list shint) (hd ht : shint)   (* [comment removed for export] *)
| RStrHex (i : nat) (segs : list (nat * list Z))  (* [comment removed for export] *)
| RIab (src : option nat) (recs : list (shint * shint)) (hd : shint)   (* [comment removed for export] *)
.

Definition knx (c : vc) : list kentry := vc_kn c ++ derived (vc_kn c) (vc_hyps c).

(* [comment removed for export] *)
Fixpoint find_s1ok (hyps : list gatom) : option (expr * expr * expr * expr) :=
  match hyps with
  | [] => None
  | GA id [b; l; a; m] :: rest => if Nat.eqb id 60 then Some (b, l, a, m) else find_s1ok rest
  | _ :: rest => find_s1ok rest
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition step_ok (kx : list kentry) (bt : expr) (d : Z) : bool :=
  let ne c := (lin_ge0 kx [(ELit (c - 1), 0)] [(bt, 0)] || lin_ge0 kx [(bt, 0)] [(ELit (c + 1), 0)])%bool in
  let is c := (lin_ge0 kx [(bt, 0)] [(ELit c, 0)] && lin_ge0 kx [(ELit c, 0)] [(bt, 0)])%bool in
  if Z.eqb d 1 then (ne 34 && ne 92)%bool else if Z.eqb d 2 then is 92 else false.
Definition byte_is34 (kn kx : list kentry) (buf x : expr) : bool :=
  match find_rec kn kn [(buf, 0); (x, 0)] 1 with
  | Some bv => lin_ge0 kx [(recval 1 bv, 0)] [(ELit 34, 0)] && lin_ge0 kx [(ELit 34, 0)] [(recval 1 bv, 0)]
  | None => false
  end.
(* [comment removed for export] *)
Fixpoint zle (zs : list Z) : Z := match zs with [] => 0 | b :: r => Z.lor b (Z.shiftl (zle r) 8) end.
Definition img_u32 (a : Z) : option Z := match img_bytes SEGS a 4 with Some zs => Some (zle zs) | None => None end.
Definition is_hexchar (b : Z) : bool := ((48 <=? b) && (b <=? 57)) || ((65 <=? b) && (b <=? 70)) || ((97 <=? b) && (b <=? 102)).
(* [comment removed for export] *)
Definition hex_tab_ok (tab : Z) : bool :=
  forallb (fun b : nat => match img_u32 (tab + 4 * Z.of_nat b) with
                         | Some v => Z.eqb v 4294967295 || is_hexchar (Z.of_nat b)
                         | None => false end) (seq 0 256).
(* [comment removed for export] *)
Fixpoint or_leaf (cp leaf : expr) : bool :=
  expr_eqb cp leaf ||
  match cp with
  | EAlu ALU_OR a b => or_leaf a leaf || or_leaf b leaf
  | _ => false
  end.
(* [comment removed for export] *)
Definition cp_bound (kx : list kentry) (i : nat) (cp : expr) : option Z :=
  match nth_error kx i with
  | Some (KRange e lo hi) =>
      if expr_eqb e cp then Some hi else
      match e with
      | EAlu ALU_SLTU (ELit cc) e' => if (expr_eqb e' cp && Z.eqb lo 0 && Z.eqb hi 0 && Z.leb 0 cc && Z.ltb cc two64)%bool then Some cc else None
      | _ => None
      end
  | _ => None
  end.
(* [comment removed for export] *)
Definition cp_boundm (kx : list kentry) (i : nat) (cp : expr) : option Z :=
  match nth_error kx i with
  | Some (KRange (EMd M_MUL (ELit m) (EAlu ALU_SRL e' (ELit s))) lo hi) =>
      if (expr_eqb e' cp && Z.ltb 0 m && Z.leb 0 s && Z.ltb s 64 && Z.leb m (2 ^ s) && Z.leb 0 hi && Z.ltb hi two64)%bool
      then Some ((hi / m + 1) * 2 ^ s - 1) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition img_covered (kn : list kentry) (a n : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb (a + n) hi | _ => false end) kn.
(* [comment removed for export] *)
Definition cp32_bound (kx : list kentry) (i : nat) : option (expr * Z) :=
  match nth_error kx i with
  | Some (KRange (EAluw ALU_SRL cp (ELit 16)) lo hi) => if Z.ltb hi 65535 then Some (cp, hi) else None
  | Some (KRange (EAlu ALU_SLTU (ELit cc) (EAluw ALU_SRL cp (ELit 16))) 0 0) =>
      if (Z.leb 0 cc && Z.ltb cc 65535)%bool then Some (cp, cc) else None
  | Some (KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_SRL cp (ELit 16)) (ELit 0)) (ELit 1)) 1 1) => Some (cp, 0)
  | _ => None
  end.
(* [comment removed for export] *)
Definition cp_of (K : kentry) : option expr :=
  match K with
  | KRange (EAlu ALU_SLTU (ELit _) e') _ _ => Some e'
  | KRange (EMd M_MUL (ELit _) (EAlu ALU_SRL e' (ELit _))) _ _ => Some e'
  | KRange e _ _ => Some e
  | _ => None
  end.
(* [comment removed for export] *)
Definition addw_lit (t : Z) : Z := (bv_swrap 32 t) mod two64.
Definition cp_excl (kx : list kentry) (i : nat) (vm : expr) : bool :=
  match nth_error kx i with
  | Some (KRange (EAlu ALU_SLTU (ELit c) (EAluw ALU_ADD e (ELit k))) 0 0) =>
      (or_leaf e vm || or_leaf e (EExt true 0 4 vm)) && (0 <=? c) && (c <? addw_lit (k mod two64 - 1))
  | _ => false
  end.
(* [comment removed for export] *)
Definition uhex_seg (c : vc) (kx : list kentry) (buf pos : expr) (icp : nat) (tabs : list Z) : bool :=
  match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (pos, 0)] 1, tabs with
  | Some bv0, [t0; t1; t2; t3] =>
      lin_ge0 kx [(recval 1 bv0, 0)] [(ELit 92, 0)] && lin_ge0 kx [(ELit 92, 0)] [(recval 1 bv0, 0)] &&
      forallb (fun mt : nat * Z =>
        let (m, tab) := mt in
        match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (pos, 2 + Z.of_nat m)] 1 with
        | Some bvm =>
            let bt := recval 1 bvm in
            match find_rec (vc_kn c) (vc_kn c) ((ELit tab, 0) :: xN 4 bt) 4 with
            | Some vm =>
                (* [comment removed for export] *)
                let ok_leaf hi := Z.ltb hi 4294967295 in
                match cp_bound kx icp vm, cp_bound kx icp (EExt true 0 4 vm) with
                | Some hi, _ => ok_leaf hi
                | None, Some hi => ok_leaf hi
                | None, None =>
                    existsb (fun K => match cp_of K with
                            | Some e => match cp_boundm kx icp e with
                                        | Some hi => (or_leaf e vm || or_leaf e (EExt true 0 4 vm)) && ok_leaf hi
                                        | None => false end
                            | None => false end) (match nth_error kx icp with Some K => [K] | None => [] end)
                    ||
                    existsb (fun K => match cp_of K with
                            | Some e => match cp_bound kx icp e with
                                        | Some hi => (or_leaf e vm || or_leaf e (EExt true 0 4 vm)) && ok_leaf hi
                                        | None => false end
                            | None => false end) (match nth_error kx icp with Some K => [K] | None => [] end)
                    || match cp32_bound kx icp with
                       | Some (e, _) => or_leaf e vm || or_leaf e (EExt true 0 4 vm)
                       | None => false end
                    || cp_excl kx icp vm                 (* [comment removed for export] *)
                end
                && img_covered (vc_kn c) tab 1024 && hex_tab_ok tab
            | None => false end
        | None => false end) (combine (seq 0 4) tabs)
  | _, _ => false
  end.
Fixpoint uhex_walk (c : vc) (kx : list kentry) (buf p : expr) (d : Z) (segs : list (nat * list Z)) : option Z :=
  match segs with
  | [] => Some d
  | (icp, tabs) :: rest => if uhex_seg c kx buf (eADDk p d) icp tabs then uhex_walk c kx buf p (d + 6) rest else None
  end.

(* [comment removed for export] *)
Definition recvalx (kx : list kentry) (v : expr) : expr :=
  if lin_ge0 kx [(ELit 4294967295, 0)] [(v, 0)] then v else recval 4 v.
Lemma recvalx_sound : forall E M kx v, know_ok SEGS E M kx -> bv_unsigned (edenot E (recvalx kx v)) = bv_unsigned (edenot E v) mod 2 ^ 32.
Proof.
  intros E M kx v HK. unfold recvalx. destruct (lin_ge0 kx [(ELit 4294967295, 0)] [(v, 0)]) eqn:H; [|apply recval4].
  pose proof (lin_ge0_sound SEGS E M kx _ _ HK H) as B. cbn [xt_den edenot] in B. rewrite u_lit64a in B.
  change (4294967295 mod 2 ^ 64) with 4294967295 in B. pose proof (u64_range (edenot E v)). symmetry. apply Z.mod_small. lia.
Qed.
Definition extra_fact (c : vc) (kx : list kentry) (x : extra) : kentry :=
  match x with
  | XIdx k h =>
      match find_s1ok (vc_hyps c) with
      | Some (buf, len, a1, n) =>
          match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 with
          | Some v => if lin_ge0_h2 kx h [(n, 0)] [(k, 1)] then KRange (eSUB len (recval 4 v)) 1 (hiZ (vc_kn c) len) else KTriv
          | None => KTriv
          end
      | None => KTriv
      end
  | XSltu i hal hau hbl hbu =>
      match nth_error (vc_kn c) i with
      | Some (KRange (EAlu ALU_SLTU a b) v v') =>
          match lin_lo_h kx hal (fst (lin_of a)) (snd (lin_of a)), lin_hi_h kx hau (fst (lin_of a)) (snd (lin_of a)),
                lin_lo_h kx hbl (fst (lin_of b)) (snd (lin_of b)), lin_hi_h kx hbu (fst (lin_of b)) (snd (lin_of b)) with
          | Some la, Some ua, Some lb, Some ub =>
              if (Z.leb 0 la && Z.ltb ua two64 && Z.leb 0 lb && Z.ltb ub two64)%bool then
                if (Z.eqb v 0 && Z.eqb v' 0)%bool then KRange (eSUB a b) 0 (ua - lb)
                else if (Z.eqb v 1 && Z.eqb v' 1)%bool then KRange (eSUB b a) 1 (ub - la)
                else KTriv
              else KTriv
          | _, _, _, _ => KTriv
          end
      | _ => KTriv
      end
  | XStrStep i d =>
      match nth_error (vc_hyps c) i with
      | Some (GA id [buf; len; a1; n; k; p]) =>
          if Nat.eqb id 61 then
            match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1 with
            | Some bv => if step_ok kx (recval 1 bv) d then KRange (eSUB len p) (d + 1) (hiZ (vc_kn c) len) else KTriv
            | None => KTriv
            end
          else KTriv
      | _ => KTriv
      end
  | XStep k h =>
      match find_s1ok (vc_hyps c) with
      | Some (buf, len, a1, n) =>
          match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4, find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4 with
          | Some v1, Some v2 =>
              match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v1, 0)] 1 with
              | Some b1 => if lin_ge0 kx [(recval 1 b1, 0)] [(ELit 1, 0)] && lin_ge0_h2 kx h [(n, 1)] [(k, 0)]
                           then KRange (eSUB (recval 4 v2) (recval 4 v1)) 1 (hiZ (vc_kn c) len) else KTriv
              | None => KTriv end
          | _, _ => KTriv end
      | None => KTriv end
  | XOc i d' h =>
      match nth_error (vc_hyps c) i with
      | Some (GA id [oc; dd; t]) =>
          if Nat.eqb id 64 then
            match find_rec (vc_kn c) (vc_kn c) ((oc, 0) :: xN 8 d') 4 with
            | Some v => if lin_ge0_h2 kx h [(dd, 0)] [(d', 0)] then KRange (eSUB t (recvalx kx v)) 1 (hiZ (vc_kn c) t) else KTriv
            | None => KTriv
            end
          else KTriv
      | _ => KTriv
      end
  | XExtEq n e hl hu =>
      match lin_lo_h kx hl (fst (lin_of e)) (snd (lin_of e)), lin_hi_h kx hu (fst (lin_of e)) (snd (lin_of e)) with
      | Some l, Some u =>
          if (Nat.ltb 0 n && Nat.leb n 8 && Z.leb 0 l && Z.ltb u (2 ^ (8 * Z.of_nat n)))%bool
          then KRange (eSUB (EExt false 0 n e) e) 0 0 else KTriv
      | _, _ => KTriv
      end
  | XUHex i segs =>
      match nth_error (vc_hyps c) i with
      | Some (GA id [buf; len; a1; n; k; p]) =>
          if Nat.eqb id 61 then
            match uhex_walk c kx buf p 0 segs with
            | Some d => KRange (eSUB len p) (d + 1) (hiZ (vc_kn c) len)
            | None => KTriv
            end
          else KTriv
      | _ => KTriv
      end
  | XIab i d' hl hu =>
      match nth_error (vc_hyps c) i with
      | Some (GA id [ia; dd]) =>
          if Nat.eqb id 65 then
            match find_rec (vc_kn c) (vc_kn c) ((ia, 0) :: xN 1 d') 1 with
            | Some v => if lin_ge0_h2 kx hl (xN 1 d') [(ELit 1, 0)] && lin_ge0_h2 kx hu [(dd, 0)] [(d', 0)]
                        then KRange (recval 1 v) 0 1 else KTriv
            | None => KTriv
            end
          else KTriv
      | _ => KTriv
      end
  | XStr k h =>
      match find_s1ok (vc_hyps c) with
      | Some (buf, len, a1, n) =>
          match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 with
          | Some v => if lin_ge0_h2 kx h [(n, 1)] [(k, 0)] && byte_is34 (vc_kn c) kx buf (recval 4 v)
                      then KRange (eSUB len (recval 4 v)) 2 (hiZ (vc_kn c) len) else KTriv
          | None => KTriv
          end
      | None => KTriv
      end
  end.
Fixpoint add_extras (c : vc) (kx : list kentry) (xs : list extra) : list kentry :=
  match xs with
  | [] => kx
  | x :: rest => add_extras c (kx ++ [extra_fact c kx x]) rest
  end.

Definition lin_eqx (kn : list kentry) (a b : xterms) : bool := lin_ge0 kn a b && lin_ge0 kn b a.
Definition byte_is (kn : list kentry) (bt : expr) (c : Z) : bool := lin_eqx kn [(bt, 0)] [(ELit c, 0)].
Definition byte_ne (kn : list kentry) (bt : expr) (c : Z) : bool :=
  lin_ge0 kn [(ELit (c - 1), 0)] [(bt, 0)] || lin_ge0 kn [(bt, 0)] [(ELit (c + 1), 0)].
Definition lit_arg (e : expr) : option Z := match e with ELit z => Some z | _ => None end.

(* [comment removed for export] *)
Definition acc_goals (kx : list kentry) (hT hS : shint) (L : expr) (dL : Z) (t' s' : expr) (tb' sb' : Z) : bool :=
  Z.leb 0 tb' && Z.ltb tb' 64 && Z.leb 0 sb' && Z.ltb sb' 64 &&
  lin_ge0_h2 kx hT [(L, dL + 2 - tb')] [(t', 0)] &&
  lin_ge0_h2 kx hS ((L, 5 * dL + sb') :: xN 4 L) (xN 3 s').

Definition check_acc_init (c : vc) (kx : list kentry) (hk ht hs : shint) (g : gatom) : bool :=
  Nat.eqb (g_id g) 62 &&
  match g_args g, find_s1ok (vc_hyps c) with
  | [a1; n; len; k; t; s; tbe; sbe], Some (buf, len0, a10, n0) =>
      match lit_arg tbe, lit_arg sbe with
      | Some tb, Some sb =>
          expr_eqb len len0 && expr_eqb a1 a10 && expr_eqb n n0 &&
          lin_ge0_h2 kx hk [(n, 0)] [(k, 0)] &&                       (* [comment removed for export] *)
          acc_goals kx ht hs k 0 t s tb sb
      | _, _ => false end
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition acc_hyp (c : vc) (i : nat) : option (list expr) :=
  match nth_error (vc_hyps c) i with
  | Some (GA id args) => if Nat.eqb id 62 then Some args else None
  | None => None
  end.
Definition str_hyp (c : vc) (i : nat) : option (list expr) :=
  match nth_error (vc_hyps c) i with
  | Some (GA id args) => if Nat.eqb id 61 then Some args else None
  | None => None
  end.
Definition oc_hyp (c : vc) (i : nat) : option (list expr) :=
  match nth_error (vc_hyps c) i with
  | Some (GA id args) => if Nat.eqb id 64 then Some args else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint adv_xs (c : vc) (kx : list kentry) (buf a1 k : expr) (j : Z) (n : nat) : option (list expr) :=
  match n with
  | O => Some []
  | S n' =>
      match find_rec (vc_kn c) (vc_kn c) ((a1, 4 * j) :: xN 4 k) 4 with
      | Some v => let x := recval 4 v in
          match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 with
          | Some bv => if lin_ge0 kx [(recval 1 bv, 0)] [(ELit 1, 0)] then
                         match adv_xs c kx buf a1 k (j + 1) n' with Some xs => Some (x :: xs) | None => None end
                       else None
          | None => None end
      | None => None end
  end.
(* [comment removed for export] *)
Fixpoint step_facts (hi : Z) (xs : list expr) : list kentry :=
  match xs with
  | x1 :: ((x2 :: _) as rest) => KRange (eSUB x2 x1) 1 hi :: step_facts hi rest
  | _ => []
  end.
Definition check_acc (c : vc) (kx : list kentry) (i : nat) (m : kmode) (hT hS : shint) (g : gatom) : bool :=
  Nat.eqb (g_id g) 62 &&
  match g_args g, acc_hyp c i, find_s1ok (vc_hyps c) with
  | [a1; n; len; k'; t'; s'; tbe'; sbe'], Some [a1h; nh; lenh; k; t; s; tbe; sbe], Some (buf, len0, a10, n0) =>
    match lit_arg tbe', lit_arg sbe', lit_arg tbe, lit_arg sbe with
    | Some tb', Some sb', Some tb, Some sb =>
        expr_eqb a1h a1 && expr_eqb nh n && expr_eqb lenh len && expr_eqb len len0 && expr_eqb a1 a10 && expr_eqb n n0 &&
        match m with
        | KSame =>
            lin_eqx kx [(k', 0)] [(k, 0)] &&
            match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 with
            | Some v => acc_goals kx hT hS (recval 4 v) 0 t' s' tb' sb'
            | None => false end
        | KSameRel =>
            lin_eqx kx [(k', 0)] [(k, 0)] &&
            Z.leb 0 tb' && Z.ltb tb' 64 && Z.leb 0 sb' && Z.ltb sb' 64 &&
            Z.leb 0 tb && Z.ltb tb 64 && Z.leb 0 sb && Z.ltb sb 64 &&
            lin_ge0_h2 kx hT [(t, tb - tb')] [(t', 0)] &&                        (* [comment removed for export] *)
            lin_ge0_h2 kx hS ((s, sb' - sb) :: xN 2 s) (xN 3 s')                 (* [comment removed for export] *)
        | KAdvNZ =>
            lin_eqx kx [(k', 0)] [(k, 1)] &&
            match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 with
            | Some v => let x := recval 4 v in
                match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 with
                | Some bv => lin_ge0 kx [(recval 1 bv, 0)] [(ELit 1, 0)] && acc_goals kx hT hS x 1 t' s' tb' sb'
                | None => false end
            | None => false end
        | KAdvStr =>
            lin_eqx kx [(k', 0)] [(k, 1)] &&
            match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 with
            | Some v => let x := recval 4 v in
                match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 with
                | Some bv => byte_is kx (recval 1 bv) 34 && acc_goals kx hT hS x 2 t' s' tb' sb'
                | None => false end
            | None => false end
        | KAdv2NZ =>
            lin_eqx kx [(k', 0)] [(k, 2)] &&
            match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4, find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4 with
            | Some v1, Some v2 => let x1 := recval 4 v1 in let x2 := recval 4 v2 in
                match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x1, 0)] 1, find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x2, 0)] 1 with
                | Some b1, Some b2 => lin_ge0 kx [(recval 1 b1, 0)] [(ELit 1, 0)] && lin_ge0 kx [(recval 1 b2, 0)] [(ELit 1, 0)] &&
                                      acc_goals kx hT hS x2 1 t' s' tb' sb'
                | _, _ => false end
            | _, _ => false end
        | KAdv2Str =>
            lin_eqx kx [(k', 0)] [(k, 2)] &&
            match find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4, find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4 with
            | Some v1, Some v2 => let x1 := recval 4 v1 in let x2 := recval 4 v2 in
                match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x1, 0)] 1, find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x2, 0)] 1 with
                | Some b1, Some b2 => lin_ge0 kx [(recval 1 b1, 0)] [(ELit 1, 0)] && byte_is kx (recval 1 b2) 34 &&
                                      acc_goals kx hT hS x2 2 t' s' tb' sb'
                | _, _ => false end
            | _, _ => false end
        | KAdvN nn str =>
            Nat.ltb 0 nn && lin_eqx kx [(k', 0)] [(k, Z.of_nat nn)] &&
            match adv_xs c kx buf a1 k 0 nn with
            | Some xs =>
                let x := nth (nn - 1) xs (ELit 0) in
                let kx2 := kx ++ step_facts (hiZ (vc_kn c) len) xs in      (* [comment removed for export] *)
                (if str then match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 with
                             | Some bv => byte_is kx (recval 1 bv) 34 | None => false end
                 else true) &&
                acc_goals kx2 hT hS x (if str then 2 else 1) t' s' tb' sb'
            | None => false end
        | KStrEnd istr =>     (* [comment removed for export] *)
            lin_eqx kx [(k', 0)] [(k, 0)] &&
            Z.leb 0 tb' && Z.ltb tb' 64 && Z.leb 0 sb' && Z.ltb sb' 64 &&
            Z.leb 0 tb && Z.ltb tb 64 && Z.leb 0 sb && Z.ltb sb 64 &&
            lin_ge0_h2 kx hT [(t, tb - tb')] [(t', 0)] &&
            match str_hyp c istr with
            | Some [bufs; lens; a1s; ns; ks; p] =>
                expr_eqb bufs buf && expr_eqb lens len && expr_eqb a1s a1 && expr_eqb ns n && lin_eqx kx [(ks, 0)] [(k, 0)] &&
                match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1 with
                | Some bv => byte_is kx (recval 1 bv) 34 && lin_ge0_h2 kx hS ((p, 5 + sb') :: xN 4 p) (xN 3 s')
                | None => false end
            | _ => false end
        end
    | _, _, _, _ => false end
  | _, _, _ => false
  end.

Definition check_str_start (c : vc) (kx : list kentry) (hk : shint) (g : gatom) : bool :=
  Nat.eqb (g_id g) 61 &&
  match g_args g, find_s1ok (vc_hyps c) with
  | [buf; len; a1; n; k; p], Some (buf0, len0, a10, n0) =>
      expr_eqb buf buf0 && expr_eqb len len0 && expr_eqb a1 a10 && expr_eqb n n0 &&
      lin_ge0 kx [(k, 0)] [(ELit 1, 0)] && lin_ge0_h2 kx hk [(n, 2)] [(k, 0)] &&        (* [comment removed for export] *)
      match find_rec (vc_kn c) (vc_kn c) ((a1, -4) :: xN 4 k) 4 with
      | Some v => let x := recval 4 v in
          lin_eqx kx [(p, 0)] [(x, 1)] &&
          match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 with
          | Some bv => byte_is kx (recval 1 bv) 34
          | None => false end
      | None => false end
  | _, _ => false
  end.

Definition check_str (c : vc) (kx : list kentry) (i : nat) (d : Z) (g : gatom) : bool :=
  Nat.eqb (g_id g) 61 &&
  match g_args g, str_hyp c i with
  | [buf; len; a1; n; k; p'], Some [bufh; lenh; a1h; nh; kh; p] =>
      expr_eqb bufh buf && expr_eqb lenh len && expr_eqb a1h a1 && expr_eqb nh n && expr_eqb kh k &&
      lin_eqx kx [(p', 0)] [(p, d)] &&
      match find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1 with
      | Some bv => let bt := recval 1 bv in
          if Z.eqb d 1 then byte_ne kx bt 34 && byte_ne kx bt 92
          else if Z.eqb d 2 then byte_is kx bt 92 else false
      | None => false end
  | _, _ => false
  end.

Fixpoint check_oc_recs (c : vc) (kx : list kentry) (oc d' t' : expr) (j : Z) (recs : list shint) : bool :=
  match recs with
  | [] => true
  | hx :: rest =>
      match find_rec (vc_kn c) (vc_kn c) ((oc, - (8 * j)) :: xN 8 d') 4 with
      | Some v => lin_ge0_h2 kx hx [(t', 0)] [(recvalx kx v, 1)] && check_oc_recs c kx oc d' t' (j + 1) rest
      | None => false
      end
  end.
Definition check_oc (c : vc) (kx : list kentry) (src : option nat) (recs : list shint) (hd ht : shint) (g : gatom) : bool :=
  Nat.eqb (g_id g) 64 &&
  match g_args g with
  | [oc; d'; t'] =>
      let nr := Z.of_nat (length recs) in
      lin_ge0 kx [] ((oc, 9 - two64) :: xN 8 d') &&                            (* [comment removed for export] *)
      (* [comment removed for export] *)
      match src with
      | Some i =>
          match oc_hyp c i with
          | Some [och; d; t] => expr_eqb och oc && lin_ge0_h2 kx ht [(t', 0)] [(t, 0)] && lin_ge0_h2 kx hd [(d, nr)] [(d', 0)]
          | _ => false end
      | None => lin_ge0_h2 kx hd [(ELit 0, nr - 1)] [(d', 0)]
      end &&
      check_oc_recs c kx oc d' t' 0 recs
  | _ => false
  end.

(* [comment removed for export] *)
Definition iab_hyp (c : vc) (i : nat) : option (list expr) :=
  match nth_error (vc_hyps c) i with
  | Some (GA id args) => if Nat.eqb id 65 then Some args else None
  | None => None
  end.
Fixpoint check_iab_recs (c : vc) (kx : list kentry) (ia d' : expr) (j : Z) (recs : list (shint * shint)) : bool :=
  match recs with
  | [] => true
  | (hl, hu) :: rest =>
      match find_rec (vc_kn c) (vc_kn c) ((ia, - j) :: xN 1 d') 1 with
      | Some v => (match v with ELit z => Z.leb 0 z && Z.leb z 1 | _ => false end     (* [comment removed for export] *)
                   || lin_ge0_h2 kx hu [(ELit 1, 0)] [(recval 1 v, 0)])                (* [comment removed for export] *)
                  && check_iab_recs c kx ia d' (j + 1) rest
      | None => false
      end
  end.
Definition check_iab (c : vc) (kx : list kentry) (src : option nat) (recs : list (shint * shint)) (hd : shint) (g : gatom) : bool :=
  Nat.eqb (g_id g) 65 &&
  match g_args g with
  | [ia; d'] =>
      let nr := Z.of_nat (length recs) in
      lin_ge0 kx [] ((ia, 2 - two64) :: xN 1 d') &&                            (* [comment removed for export] *)
      match src with
      | Some i =>
          match iab_hyp c i with
          | Some [iah; d] => expr_eqb iah ia && lin_ge0_h2 kx hd [(d, nr)] [(d', 0)]
          | _ => false end
      | None => lin_ge0_h2 kx hd [(ELit 0, nr)] [(d', 0)]
      end &&
      check_iab_recs c kx ia d' 0 recs
  | _ => false
  end.

Definition check_strhex (c : vc) (kx : list kentry) (i : nat) (segs : list (nat * list Z)) (g : gatom) : bool :=
  Nat.eqb (g_id g) 61 &&
  match g_args g, str_hyp c i with
  | [buf; len; a1; n; k; p'], Some [bufh; lenh; a1h; nh; kh; p] =>
      expr_eqb bufh buf && expr_eqb lenh len && expr_eqb a1h a1 && expr_eqb nh n && expr_eqb kh k &&
      match uhex_walk c kx buf p 0 segs with
      | Some d => lin_eqx kx [(p', 0)] [(p, d)]
      | None => false
      end
  | _, _ => false
  end.

Definition vc_check (r : rule) (c : vc) : bool :=
  match r, vc_concl c with
  | RHyp i, VCAtom g => match nth_error (vc_hyps c) i with Some g' => gatom_eqb g' g | None => false end
  | RLin xs hl hu, VCFact (KRange e lo hi) => krange_h2 (add_extras c (knx c) xs) hl hu e lo hi
  | RAccInit hk ht hs, VCAtom g => check_acc_init c (knx c) hk ht hs g
  | RAcc i m hT hS, VCAtom g => check_acc c (knx c) i m hT hS g
  | RStrStart hk, VCAtom g => check_str_start c (knx c) hk g
  | RStr i d, VCAtom g => check_str c (knx c) i d g
  | ROc src recs hd ht, VCAtom g => check_oc c (knx c) src recs hd ht g
  | RStrHex i segs, VCAtom g => check_strhex c (knx c) i segs g
  | RIab src recs hd, VCAtom g => check_iab c (knx c) src recs hd g
  | _, _ => false
  end.

Fixpoint vcs_check (rs : list rule) (cs : list vc) : bool :=
  match rs, cs with
  | [], [] => true
  | r :: rs', c :: cs' => vc_check r c && vcs_check rs' cs'
  | _, _ => false
  end.

Section CheckSound.
Lemma knx_sound : forall E M c, know_ok SEGS E M (vc_kn c) -> Forall (APS.gholds GP2 E M) (vc_hyps c) ->
  know_ok SEGS E M (knx c).
Proof. intros E M c Hk Hh. unfold knx. apply Forall_app. split; [exact Hk | apply derived_sound; assumption]. Qed.

Lemma gatom_eqb_eq : forall a b, gatom_eqb a b = true -> a = b.
Proof.
  intros [i xs] [j ys] H. unfold gatom_eqb in H. cbn [g_id g_args] in H. apply andb_prop in H as [Hi Hl].
  apply Nat.eqb_eq in Hi. subst j. f_equal. exact (APS.list_eqb_eq expr_eqb expr_eqb_eq _ _ Hl).
Qed.

(* [comment removed for export] *)
Lemma zle_bytes : forall bs, bytes_le_to_Z bs = zle (map bv_unsigned bs).
Proof. induction bs as [|b r IH]; [reflexivity|]. cbn [bytes_le_to_Z zle map]. rewrite IH. reflexivity. Qed.

Lemma rdn_none_img : forall mem n (a : word) bs,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64) ->
  (forall j, (j < n)%nat -> mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  rdn SEGS mem a n = Some bs -> img_bytes SEGS (bv_unsigned a) n = Some (map bv_unsigned bs).
Proof.
  intros mem n. induction n as [|n IH]; intros a bs Hnw Hnone H.
  - cbn in H. injection H as <-. reflexivity.
  - cbn [rdn] in H. pose proof (Hnone 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0 in H.
    cbn [img_bytes]. rewrite Z_to_bv_bv_unsigned.
    destruct (seg_rom SEGS a) as [b|]; [|discriminate].
    destruct (rdn SEGS mem (a + 1) n) as [rest|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct n as [|n'].
    { cbn in Hr. injection Hr as <-. reflexivity. }
    assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite <- Hu1. rewrite (IH (a + 1)%bv rest); [reflexivity | rewrite Hu1; lia | | exact Hr].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia. apply Hnone. lia.
Qed.

Lemma img_covered_sound : forall E M kn a n, know_ok SEGS E M kn -> img_covered kn a n = true ->
  exists lo hi, lo <= a /\ a + n <= hi /\ hi <= 2 ^ 64 /\ forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M kn a n Hkn H. unfold img_covered in H. apply existsb_exists in H as (K & HK & Hb).
  destruct K as [| | |lo hi| | | | | |]; try discriminate. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hkn _ HK) as KK. cbn [kentry_ok] in KK. destruct KK as (A & B & C).
  exists lo, hi. repeat split; try lia. exact C.
Qed.

(* [comment removed for export] *)
Lemma img_rec_value : forall E M kn tab bt v, know_ok SEGS E M kn ->
  find_rec kn kn ((ELit tab, 0) :: xN 4 bt) 4 = Some v -> img_covered kn tab 1024 = true ->
  0 <= tab -> tab + 1024 <= two64 -> uD E bt <= 255 ->
  img_u32 (tab + 4 * uD E bt) = Some (uD E v mod 2 ^ 32).
Proof.
  intros E M kn tab bt v Hkn Hr Hc Ht0 Ht1 Hb.
  destruct (find_rec_sound E M kn kn _ 4 v Hkn Hkn Hr) as (_ & Hge & Hle & Hrd).
  cbn [xt_den edenot] in Hrd, Hge, Hle. rewrite xt_den_xN, u_lit64a in Hrd, Hge, Hle. unfold two64 in Ht1.
  rewrite (Z.mod_small tab) in Hrd, Hge, Hle by lia. replace (Z.of_nat 4) with 4 in Hrd, Hge, Hle by reflexivity.
  pose proof (u64_range (edenot E bt)) as RB.
  replace (tab + 0 + 4 * bv_unsigned (edenot E bt)) with (tab + 4 * uD E bt) in Hrd, Hge, Hle by lia.
  destruct (img_covered_sound E M kn tab 1024 Hkn Hc) as (lo & hi & L1 & L2 & L3 & NONE).
  assert (Hu : bv_unsigned (Z_to_bv 64 (tab + 4 * uD E bt)) = tab + 4 * uD E bt).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  pose proof (rdn_none_img M 4 (Z_to_bv 64 (tab + 4 * uD E bt)) _ ltac:(rewrite Hu; cbn; lia)
                ltac:(intros j Hj; rewrite Hu; apply NONE; lia) Hrd) as IMG.
  rewrite Hu in IMG. unfold img_u32. rewrite IMG. f_equal. rewrite <- zle_bytes, bytes_le_N. reflexivity.
Qed.

Lemma hex_tab_ok_sound : forall tab b v, hex_tab_ok tab = true -> 0 <= b <= 255 -> img_u32 (tab + 4 * b) = Some v ->
  v <> 4294967295 -> is_hexchar b = true.
Proof.
  intros tab b v H Hb Hv Hne. unfold hex_tab_ok in H.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat b) ltac:(apply in_seq; lia)) as Hx. cbn beta in Hx.
  rewrite Z2Nat.id in Hx by lia. rewrite Hv in Hx. apply Bool.orb_prop in Hx as [Hx|Hx]; [|exact Hx].
  apply Z.eqb_eq in Hx. lia.
Qed.
Lemma is_hexchar_nq : forall b, is_hexchar b = true -> b <> 34 /\ b <> 92.
Proof.
  intros b H. unfold is_hexchar in H.
  repeat (apply Bool.orb_prop in H as [H|H]); apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
Qed.

(* [comment removed for export] *)
Lemma sx_all_ones : forall E v, uD E v mod 2 ^ 32 = 4294967295 -> uD E (EExt true 0 4 v) = 2 ^ 64 - 1.
Proof.
  intros E v H. cbn [edenot]. unfold ext_val, ext_Z. lazymatch goal with |- ?g => idtac end.
  replace (bv_unsigned (edenot E v) / 2 ^ (8 * Z.of_nat 0)) with (bv_unsigned (edenot E v)) by (cbn; rewrite Z.div_1_r; reflexivity).
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity. rewrite H. reflexivity.
Qed.
Lemma or_leaf_sound : forall E cp leaf, or_leaf cp leaf = true -> uD E leaf <= uD E cp.
Proof.
  intros E cp leaf. induction cp as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros H;
    cbn [or_leaf] in H; (destruct (expr_eqb _ leaf) eqn:He; [apply expr_eqb_eq in He; rewrite <- He; lia|]); cbn [orb] in H; try discriminate.
  destruct op; try discriminate.
  cbn [edenot]. rewrite u_or64. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  apply Bool.orb_prop in H as [H|H].
  + pose proof (IHa H). pose proof (lor_ge_l (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) ltac:(lia) ltac:(lia)). lia.
  + pose proof (IHb H). pose proof (lor_ge_r (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma cp_bound_sound : forall E M kx i cp hi, know_ok SEGS E M kx -> cp_bound kx i cp = Some hi -> uD E cp <= hi.
Proof.
  intros E M kx i cp hi Hkx H. unfold cp_bound in H. destruct (nth_error kx i) as [K|] eqn:Hi; [|discriminate].
  assert (KK : kentry_ok SEGS E M K) by (apply (proj1 (Forall_forall _ _) Hkx); eapply nth_error_In; exact Hi).
  destruct K as [| | | | |e lo hi'| | | |]; try discriminate. cbn [kentry_ok] in KK.
  destruct (expr_eqb e cp) eqn:He.
  - apply expr_eqb_eq in He. subst. injection H as <-. lia.
  - destruct e as [| |op a e'| | | | |]; try discriminate. destruct op; try discriminate. destruct a as [cc| | | | | | |]; try discriminate.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
    repeat (apply andb_prop in Hc as [Hc ?X]). apply expr_eqb_eq in Hc. subst e'.
    apply Z.eqb_eq in X2. apply Z.eqb_eq in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X. subst. unfold two64 in X.
    cbn [edenot] in KK. rewrite u_sltu64, u_lit64a, Z.mod_small in KK by lia.
    destruct (Z.ltb_spec cc (bv_unsigned (edenot E cp))); lia.
Qed.

Lemma cp_boundm_sound : forall E M kx i cp hi, know_ok SEGS E M kx -> cp_boundm kx i cp = Some hi -> uD E cp <= hi.
Proof.
  intros E M kx i cp hi Hkx H. unfold cp_boundm in H. destruct (nth_error kx i) as [K|] eqn:Hi; [|discriminate].
  assert (KK : kentry_ok SEGS E M K) by (apply (proj1 (Forall_forall _ _) Hkx); eapply nth_error_In; exact Hi).
  destruct K as [| | | | |e lo hi'| | | |]; try discriminate.
  destruct e as [| | | |op a b| | |]; try discriminate. destruct op; try discriminate. destruct a as [m| | | | | | |]; try discriminate.
  destruct b as [| |op2 e' sh| | | | |]; try discriminate. destruct op2; try discriminate. destruct sh as [sh| | | | | | |]; try discriminate.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  repeat (apply andb_prop in Hc as [Hc ?X]). apply expr_eqb_eq in Hc. subst e'.
  apply Z.ltb_lt in X4. apply Z.leb_le in X3. apply Z.ltb_lt in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
  unfold two64 in X.
  cbn [kentry_ok edenot] in KK. rewrite u_mul64, u_lit64a, u_srl64, u_lit64a in KK.
  assert (S64 : 2 ^ sh < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  rewrite (Z.mod_small sh (2 ^ 64)) in KK by lia. rewrite (Z.mod_small sh 64) in KK by lia. rewrite (Z.mod_small m (2 ^ 64)) in KK by lia.
  pose proof (u64_range (edenot E cp)) as RC. set (c := bv_unsigned (edenot E cp)) in *.
  assert (P0 : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (Q0 : 0 <= c / 2 ^ sh) by (apply Z.div_pos; lia).
  assert (Q1 : c / 2 ^ sh <= c) by (apply Z.div_le_upper_bound; [lia|nia]).
  assert (NW : m * (c / 2 ^ sh) < 2 ^ 64).
  { apply Z.le_lt_trans with (2 ^ sh * (c / 2 ^ sh)); [nia|]. pose proof (Z.mul_div_le c (2 ^ sh) ltac:(lia)). lia. }
  rewrite Z.mod_small in KK by nia.
  assert (D1 : c / 2 ^ sh <= hi' / m). { apply Z.div_le_lower_bound; [lia|]. nia. }
  pose proof (Z.mul_succ_div_gt c (2 ^ sh) ltac:(lia)) as G. nia.
Qed.

Lemma qsearch_plain_step : forall b f q j, S1M.qsearch b f q = Some j -> b q <> 34 -> b q <> 92 ->
  exists f', S1M.qsearch b f' (q + 1) = Some j.
Proof.
  intros b f q j H H1 H2. destruct f as [|f]; cbn [S1M.qsearch] in H; [discriminate|].
  change S1M.QUOTE with 34 in H. change S1M.BACKSLASH with 92 in H.
  destruct (Z.eqb_spec (b q) 34); [lia|]. destruct (Z.eqb_spec (b q) 92); [lia|]. exists f. exact H.
Qed.
Lemma qsearch_bs_step : forall b f q j, S1M.qsearch b f q = Some j -> b q = 92 -> exists f', S1M.qsearch b f' (q + 2) = Some j.
Proof.
  intros b f q j H H1. destruct f as [|f]; cbn [S1M.qsearch] in H; [discriminate|].
  change S1M.QUOTE with 34 in H. change S1M.BACKSLASH with 92 in H.
  destruct (Z.eqb_spec (b q) 34); [lia|]. destruct (Z.eqb_spec (b q) 92); [|lia]. exists f. exact H.
Qed.

Lemma u_srlw16 : forall E a, uD E (EAluw ALU_SRL a (ELit 16)) = (uD E a mod 2 ^ 32) / 2 ^ 16.
Proof.
  intros E a. cbn [edenot]. rewrite w_srlw. unfold v_srlw. rewrite u_lit64a. cbn [edenot].
  rewrite (u_lit64a 16). change (16 mod 2 ^ 64) with 16. change (16 mod 32) with 16.
  rewrite bv_wrap32_mod, Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ 32) ltac:(lia)) as HB.
  assert (HQ : 0 <= bv_unsigned (edenot E a) mod 2 ^ 32 / 2 ^ 16 < 2 ^ 16).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 16 * 2 ^ 16) with (2 ^ 32). lia. }
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.
Lemma or_leaf32_sound : forall E cp leaf, or_leaf cp leaf = true -> uD E leaf mod 2 ^ 32 <= uD E cp mod 2 ^ 32.
Proof.
  intros E cp leaf. induction cp as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros H;
    cbn [or_leaf] in H; (destruct (expr_eqb _ leaf) eqn:He; [apply expr_eqb_eq in He; rewrite <- He; lia|]); cbn [orb] in H; try discriminate.
  destruct op; try discriminate.
  cbn [edenot]. rewrite u_or64, lor_mod_pow2 by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned (edenot E b)) (2 ^ 32) ltac:(lia)).
  apply Bool.orb_prop in H as [H|H].
  + pose proof (IHa H). pose proof (lor_ge_l (bv_unsigned (edenot E a) mod 2 ^ 32) (bv_unsigned (edenot E b) mod 2 ^ 32) ltac:(lia) ltac:(lia)). lia.
  + pose proof (IHb H). pose proof (lor_ge_r (bv_unsigned (edenot E a) mod 2 ^ 32) (bv_unsigned (edenot E b) mod 2 ^ 32) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma cp32_bound_sound : forall E M kx i cp B, know_ok SEGS E M kx -> cp32_bound kx i = Some (cp, B) ->
  0 <= B < 65535 /\ uD E cp mod 2 ^ 32 < (B + 1) * 2 ^ 16.
Proof.
  intros E M kx i cp B Hkx H. unfold cp32_bound in H. destruct (nth_error kx i) as [K|] eqn:Hi; [|discriminate].
  assert (KK : kentry_ok SEGS E M K) by (apply (proj1 (Forall_forall _ _) Hkx); eapply nth_error_In; exact Hi).
  assert (DIV : forall x Bq, 0 <= x -> x / 2 ^ 16 <= Bq -> x < (Bq + 1) * 2 ^ 16).
  { intros x Bq Hx Hq. pose proof (Z.mul_succ_div_gt x (2 ^ 16) ltac:(lia)). nia. }
  assert (SIXTEEN : forall s16 : Z, s16 <> 16 -> forall T (x : T) (f : T),
            match s16 with 16 => x | _ => f end = f).
  { intros s16 Hs T x f. destruct s16 as [|p|p]; try reflexivity. repeat (destruct p as [p|p|]; try reflexivity). lia. }
  destruct K as [| | | | |e lo hi| | | |]; try discriminate.
  destruct e as [| |op a b|op a b| | | |]; try discriminate.
  - (* [comment removed for export] *) destruct op; try discriminate.
    destruct a as [cc| |op2 a2 b2| | | | |]; try discriminate.
    + (* [comment removed for export] *)
      destruct b as [| | |opw cw sw| | | |]; try discriminate. destruct opw; try discriminate. destruct sw as [s16| | | | | | |]; try discriminate.
      destruct (Z.eq_dec s16 16) as [->|Hs]. 2: { rewrite (SIXTEEN s16 Hs) in H. discriminate. }
      destruct lo as [|l|l]; try discriminate. destruct hi as [|h|h]; try discriminate.
      destruct (Z.leb 0 cc && Z.ltb cc 65535)%bool eqn:Hc; [|discriminate]. injection H as E1 E2. subst cp B.
      apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      cbn [kentry_ok] in KK. change (edenot E (EAlu ALU_SLTU (ELit cc) (EAluw ALU_SRL cw (ELit 16))))
        with (alu64 ALU_SLTU (edenot E (ELit cc)) (edenot E (EAluw ALU_SRL cw (ELit 16)))) in KK.
      rewrite u_sltu64 in KK. pose proof (u_srlw16 E cw) as W.
      change (bv_unsigned (edenot E (ELit cc))) with (bv_unsigned (Z_to_bv 64 cc)) in KK. rewrite u_lit64a, Z.mod_small in KK by lia.
      change (bv_unsigned (edenot E (EAluw ALU_SRL cw (ELit 16)))) with (uD E (EAluw ALU_SRL cw (ELit 16))) in KK. rewrite W in KK.
      pose proof (Z.mod_pos_bound (bv_unsigned (edenot E cw)) (2 ^ 32) ltac:(lia)) as MB.
      destruct (Z.ltb_spec cc (bv_unsigned (edenot E cw) mod 2 ^ 32 / 2 ^ 16)); [lia|].
      split; [lia|]. apply DIV; lia.
    + (* [comment removed for export] *)
      destruct op2; try discriminate.
      destruct a2 as [| | |opw cw sw| | | |]; try discriminate. destruct opw; try discriminate. destruct sw as [s16| | | | | | |]; try discriminate.
      destruct (Z.eq_dec s16 16) as [->|Hs]. 2: { rewrite (SIXTEEN s16 Hs) in H. discriminate. }
      destruct b2 as [z0| | | | | | |]; try discriminate. destruct z0; try discriminate.
      destruct b as [z1| | | | | | |]; try discriminate. destruct z1 as [|p|p]; try discriminate. destruct p; try discriminate.
      destruct lo as [|l|l]; try discriminate. destruct l; try discriminate. destruct hi as [|h|h]; try discriminate. destruct h; try discriminate.
      injection H as E1 E2. subst cp B. cbn [kentry_ok] in KK.
      change (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_SRL cw (ELit 16)) (ELit 0)) (ELit 1)))
        with (alu64 ALU_SLTU (alu64 ALU_SUB (edenot E (EAluw ALU_SRL cw (ELit 16))) (edenot E (ELit 0))) (edenot E (ELit 1))) in KK.
      rewrite u_sltu64, u_sub64 in KK. pose proof (u_srlw16 E cw) as W.
      change (bv_unsigned (edenot E (EAluw ALU_SRL cw (ELit 16)))) with (uD E (EAluw ALU_SRL cw (ELit 16))) in KK. rewrite W in KK.
      change (bv_unsigned (edenot E (ELit 0))) with (bv_unsigned (Z_to_bv 64 0)) in KK.
      change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in KK. rewrite !u_lit64a in KK.
      change (0 mod 2 ^ 64) with 0 in KK. change (1 mod 2 ^ 64) with 1 in KK. rewrite Z.sub_0_r in KK.
      pose proof (Z.mod_pos_bound (bv_unsigned (edenot E cw)) (2 ^ 32) ltac:(lia)) as MB.
      assert (HQ : 0 <= bv_unsigned (edenot E cw) mod 2 ^ 32 / 2 ^ 16 < 2 ^ 16).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 16 * 2 ^ 16) with (2 ^ 32). lia. }
      rewrite Z.mod_small in KK by lia.
      destruct (Z.ltb_spec (bv_unsigned (edenot E cw) mod 2 ^ 32 / 2 ^ 16) 1); [|lia].
      split; [lia|]. apply DIV; lia.
  - (* [comment removed for export] *)
    destruct op; try discriminate. rename a into cw. destruct b as [s16| | | | | | |]; try discriminate.
    destruct (Z.eq_dec s16 16) as [->|Hs]. 2: { rewrite (SIXTEEN s16 Hs) in H. discriminate. }
    destruct (Z.ltb hi 65535) eqn:Hh; [|discriminate]. injection H as E1 E2. subst cp B. apply Z.ltb_lt in Hh.
    cbn [kentry_ok] in KK. pose proof (u_srlw16 E cw) as W.
    change (bv_unsigned (edenot E (EAluw ALU_SRL cw (ELit 16)))) with (uD E (EAluw ALU_SRL cw (ELit 16))) in KK. rewrite W in KK.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E cw)) (2 ^ 32) ltac:(lia)) as MB.
    assert (0 <= bv_unsigned (edenot E cw) mod 2 ^ 32 / 2 ^ 16) by (apply Z.div_pos; lia).
    split; [lia|]. apply DIV; lia.
Qed.

Lemma u_addw_allones : forall E e k, uD E e mod 2 ^ 32 = 4294967295 ->
  uD E (EAluw ALU_ADD e (ELit k)) = addw_lit (k mod two64 - 1).
Proof.
  intros E e k H. cbn [edenot]. rewrite w_addw. unfold v_addw. rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold addw_lit, two64. f_equal.
  rewrite u_lit64a.
  rewrite <- (bv_swrap_wrap' 32 (bv_unsigned (edenot E e) + _)), <- (bv_swrap_wrap' 32 (k mod 2 ^ 64 - 1)). rewrite !bv_wrap32_mod. f_equal.
  rewrite <- (Z.add_mod_idemp_l (bv_unsigned (edenot E e))) by lia. rewrite H.
  replace (4294967295 + k mod 2 ^ 64) with (k mod 2 ^ 64 - 1 + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma cp_excl_sound : forall E M kx i vm, know_ok SEGS E M kx -> cp_excl kx i vm = true -> uD E vm mod 2 ^ 32 <> 4294967295.
Proof.
  intros E M kx i vm Hkx H HX. unfold cp_excl in H. destruct (nth_error kx i) as [K|] eqn:Hi; [|discriminate].
  assert (KK : kentry_ok SEGS E M K) by (apply (proj1 (Forall_forall _ _) Hkx); eapply nth_error_In; exact Hi).
  destruct K as [| | | | |f lo hi| | | |]; try discriminate.
  destruct f as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate. destruct a as [c| | | | | | |]; try discriminate.
  destruct b as [| | |op e kk| | | |]; try discriminate. destruct op; try discriminate. destruct kk as [k| | | | | | |]; try discriminate.
  destruct lo; try discriminate. destruct hi; try discriminate.
  apply andb_prop in H as [H HC]. apply andb_prop in H as [HO Hc0]. apply Z.leb_le in Hc0. apply Z.ltb_lt in HC.
  assert (HE : uD E e mod 2 ^ 32 = 4294967295).
  { pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e)) (2 ^ 32) ltac:(lia)).
    apply Bool.orb_prop in HO as [HO|HO]; pose proof (or_leaf32_sound E e _ HO) as OL.
    - rewrite HX in OL. lia.
    - rewrite (sx_all_ones E vm HX) in OL. change ((2 ^ 64 - 1) mod 2 ^ 32) with 4294967295 in OL. lia. }
  pose proof (u_addw_allones E e k HE) as HA.
  cbn [kentry_ok] in KK. cbn [edenot] in KK. rewrite u_sltu64, u_lit64a in KK.
  change (bv_unsigned (edenot E (EAluw ALU_ADD e (ELit k)))) with (uD E (EAluw ALU_ADD e (ELit k))) in KK.
  cbn [edenot] in HA. rewrite HA in KK.
  assert (HB : addw_lit (k mod two64 - 1) < 2 ^ 64) by (unfold addw_lit, two64; apply Z.mod_pos_bound; lia).
  rewrite Z.mod_small in KK by lia.
  destruct (Z.ltb_spec c (addw_lit (k mod two64 - 1))); lia.
Qed.
Lemma uhex_seg_sound : forall E M c kx buf len bs pos icp tabs,
  know_ok SEGS E M (vc_kn c) -> know_ok SEGS E M kx ->
  0 <= uD E buf -> uD E buf + uD E len + 64 < two64 -> 0 <= uD E len -> input M (uD E buf) (uD E len) = Some bs ->
  uD E pos < uD E len ->
  uhex_seg c kx buf pos icp tabs = true ->
  nthb bs (uD E pos) = 92 /\ forall m, 0 <= m < 4 -> nthb bs (uD E pos + 2 + m) <> 34 /\ nthb bs (uD E pos + 2 + m) <> 92.
Proof.
  intros E M c kx buf len bs pos icp tabs Hk Hkx Hb Hbl Hl Hin Hpos H. unfold uhex_seg in H.
  destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (pos, 0)] 1) as [bv0|] eqn:Hr0; [|discriminate].
  destruct tabs as [|t0 [|t1 [|t2 [|t3 [|? ?]]]]]; try discriminate.
  apply andb_prop in H as [H HM]. apply andb_prop in H as [B1 B2].
  pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B1) as C1. pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B2) as C2.
  cbn [xt_den edenot] in C1, C2. rewrite u_lit64a, Z.mod_small in C1, C2 by lia.
  pose proof (u64_range (edenot E pos)) as RP.
  pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (pos, 0)] bv0 Hb Hbl Hl Hin Hk Hr0) as IB0.
  cbn [xt_den] in IB0. replace (uD E buf + 0 + (uD E pos + 0 + 0) - uD E buf) with (uD E pos) in IB0 by lia.
  specialize (IB0 ltac:(lia)).
  split; [lia|].
  intros m Hm.
  assert (HMm : forall mt, In mt (combine (seq 0 4) [t0; t1; t2; t3]) -> _ ) by (intros mt Hmt; exact (proj1 (forallb_forall _ _) HM mt Hmt)).
  assert (Hin4 : In (Z.to_nat m, nth (Z.to_nat m) [t0; t1; t2; t3] 0) (combine (seq 0 4) [t0; t1; t2; t3])).
  { assert (Z.to_nat m = 0 \/ Z.to_nat m = 1 \/ Z.to_nat m = 2 \/ Z.to_nat m = 3)%nat as [E0|[E0|[E0|E0]]] by lia; rewrite E0; cbn; tauto. }
  specialize (HMm _ Hin4). cbn beta iota in HMm.
  set (tab := nth (Z.to_nat m) [t0; t1; t2; t3] 0) in HMm.
  rewrite Z2Nat.id in HMm by lia.
  destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (pos, 2 + m)] 1) as [bvm|] eqn:Hrm; [|discriminate].
  destruct (find_rec (vc_kn c) (vc_kn c) ((ELit tab, 0) :: xN 4 (recval 1 bvm)) 4) as [vm|] eqn:Htm; [|discriminate].
  apply andb_prop in HMm as [HMm HT]. apply andb_prop in HMm as [HC HIC].
  (* [comment removed for export] *)
  pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (pos, 2 + m)] bvm Hb Hbl Hl Hin Hk Hrm) as IBm.
  cbn [xt_den] in IBm. replace (uD E buf + 0 + (uD E pos + (2 + m) + 0) - uD E buf) with (uD E pos + 2 + m) in IBm by lia.
  specialize (IBm ltac:(lia)).
  pose proof (recval1 E bvm) as RB. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E bvm)) (2 ^ 8) ltac:(lia)) as RB2.
  change (2 ^ 8) with 256 in RB, RB2.
  (* [comment removed for export] *)
  destruct (img_covered_sound E M (vc_kn c) tab 1024 Hk HIC) as (lo & hi & L1 & L2 & L3 & NONE).
  assert (KI : exists lo' hi', In (KImg lo' hi') (vc_kn c) /\ lo' <= tab).
  { unfold img_covered in HIC. apply existsb_exists in HIC as (K & HK1 & HK2). destruct K as [| | |lo' hi'| | | | | |]; try discriminate.
    apply andb_prop in HK2 as [X1 X2]. apply Z.leb_le in X1. exists lo', hi'. split; [exact HK1 | exact X1]. }
  destruct KI as (lo' & hi' & KIn & Klo). pose proof (proj1 (Forall_forall _ _) Hk _ KIn) as KK. cbn [kentry_ok] in KK.
  pose proof (img_rec_value E M (vc_kn c) tab (recval 1 bvm) vm Hk Htm HIC ltac:(lia) ltac:(unfold two64; lia) ltac:(lia)) as IMG.
  (* [comment removed for export] *)
  pose proof (u64_range (edenot E vm)) as RV.
  assert (LE1 : uD E vm mod 2 ^ 32 <= uD E vm) by (apply Z.mod_le; lia).
  assert (NE : uD E vm mod 2 ^ 32 <> 4294967295).
  { intros HX. pose proof (sx_all_ones E vm HX) as SX.
    destruct (cp_bound kx icp vm) as [hb|] eqn:Hcb.
    { apply Z.ltb_lt in HC. pose proof (cp_bound_sound E M kx icp _ _ Hkx Hcb). lia. }
    destruct (cp_bound kx icp (EExt true 0 4 vm)) as [hb|] eqn:Hcb1.
    { apply Z.ltb_lt in HC. pose proof (cp_bound_sound E M kx icp _ _ Hkx Hcb1). lia. }
    apply Bool.orb_prop in HC as [HC|HC]; [|exact (cp_excl_sound E M kx icp vm Hkx HC HX)].
    apply Bool.orb_prop in HC as [HC|HC].
    2: { destruct (cp32_bound kx icp) as [[e B]|] eqn:H32; [|discriminate].
         destruct (cp32_bound_sound E M kx icp e B Hkx H32) as [HB1 HB2].
         pose proof (Z.mod_pos_bound (bv_unsigned (edenot E vm)) (2 ^ 32) ltac:(lia)).
         apply Bool.orb_prop in HC as [HO|HO]; pose proof (or_leaf32_sound E e _ HO) as OL.
         - rewrite HX in OL. nia.
         - assert (LOW : uD E (EExt true 0 4 vm) mod 2 ^ 32 = 4294967295) by (rewrite SX; reflexivity). rewrite LOW in OL. nia. }
    apply Bool.orb_prop in HC as [HC|HC].
    { (* [comment removed for export] *)
      destruct (nth_error kx icp) as [K|] eqn:Hi; [|cbn in HC; discriminate]. cbn [existsb] in HC. rewrite Bool.orb_false_r in HC.
      destruct (cp_of K) as [e|]; [|discriminate].
      destruct (cp_boundm kx icp e) as [hb|] eqn:Hcb2; [|discriminate]. apply andb_prop in HC as [HO HB].
      apply Z.ltb_lt in HB. pose proof (cp_boundm_sound E M kx icp _ _ Hkx Hcb2).
      apply Bool.orb_prop in HO as [HO|HO]; pose proof (or_leaf_sound E e _ HO); lia. }
    destruct (nth_error kx icp) as [K|] eqn:Hi; [|cbn in HC; discriminate]. cbn [existsb] in HC. rewrite Bool.orb_false_r in HC.
    destruct (cp_of K) as [e|]; [|discriminate].
    destruct (cp_bound kx icp e) as [hb|] eqn:Hcb2; [|discriminate]. apply andb_prop in HC as [HO HB].
    apply Z.ltb_lt in HB. pose proof (cp_bound_sound E M kx icp _ _ Hkx Hcb2).
    apply Bool.orb_prop in HO as [HO|HO]; pose proof (or_leaf_sound E e _ HO); lia. }
  pose proof (hex_tab_ok_sound tab (uD E (recval 1 bvm)) _ HT ltac:(lia) IMG NE) as HEX.
  apply is_hexchar_nq in HEX. rewrite IBm. exact HEX.
Qed.

Lemma uhex_walk_sound : forall E M c kx buf len bs j segs, know_ok SEGS E M (vc_kn c) -> know_ok SEGS E M kx ->
  0 <= uD E buf -> uD E buf + uD E len + 64 < two64 -> 0 <= uD E len -> input M (uD E buf) (uD E len) = Some bs -> j < uD E len ->
  forall p d d', 0 <= d -> (exists fq, S1M.qsearch (nthb bs) fq (uD E p + d) = Some j) ->
  uhex_walk c kx buf p d segs = Some d' -> d <= d' /\ exists fq', S1M.qsearch (nthb bs) fq' (uD E p + d') = Some j.
Proof.
  intros E M c kx buf len bs j segs Hk Hkx Hb Hbl Hl Hin Hj. induction segs as [|[icp tabs] rest IH]; intros p d d' Hd [fq Hq] H; cbn [uhex_walk] in H.
  - injection H as <-. split; [lia|]. exists fq. exact Hq.
  - destruct (uhex_seg c kx buf (eADDk p d) icp tabs) eqn:Hs; [|discriminate].
    pose proof (S1M.qsearch_ge _ _ _ _ Hq) as [G1 G2]. pose proof (u64_range (edenot E p)) as RP.
    assert (HP : uD E (eADDk p d) = uD E p + d).
    { rewrite u_eADDk. apply Z.mod_small. unfold two64 in Hbl. lia. }
    destruct (uhex_seg_sound E M c kx buf len bs (eADDk p d) icp tabs Hk Hkx Hb Hbl Hl Hin ltac:(rewrite HP; lia) Hs) as [B0 BM].
    rewrite HP in B0, BM.
    destruct (qsearch_bs_step _ _ _ _ Hq B0) as [f1 Q1].
    destruct (qsearch_plain_step _ _ _ _ Q1 ltac:(destruct (BM 0 ltac:(lia)) as [X _]; rewrite <- (Z.add_0_r (uD E p + d + 2)); exact X)
                ltac:(destruct (BM 0 ltac:(lia)) as [_ X]; rewrite <- (Z.add_0_r (uD E p + d + 2)); exact X)) as [f2 Q2].
    replace (uD E p + d + 2 + 0 + 1) with (uD E p + d + 2 + 1) in Q2 by lia.
    destruct (qsearch_plain_step _ _ _ _ Q2 ltac:(apply (BM 1); lia) ltac:(apply (BM 1); lia)) as [f3 Q3].
    replace (uD E p + d + 2 + 1 + 1) with (uD E p + d + 2 + 2) in Q3 by lia.
    destruct (qsearch_plain_step _ _ _ _ Q3 ltac:(apply (BM 2); lia) ltac:(apply (BM 2); lia)) as [f4 Q4].
    replace (uD E p + d + 2 + 2 + 1) with (uD E p + d + 2 + 3) in Q4 by lia.
    destruct (qsearch_plain_step _ _ _ _ Q4 ltac:(apply (BM 3); lia) ltac:(apply (BM 3); lia)) as [f5 Q5].
    replace (uD E p + d + 2 + 3 + 1) with (uD E p + (d + 6)) in Q5 by lia.
    destruct (IH p (d + 6) d' ltac:(lia) ltac:(exists f5; exact Q5) H) as [D' FIN]. split; [lia | exact FIN].
Qed.

Lemma find_s1ok_sound : forall E M hyps buf len a1 n, Forall (APS.gholds GP2 E M) hyps -> find_s1ok hyps = Some (buf, len, a1, n) ->
  p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M.
Proof.
  intros E M hyps buf len a1 n Hh. induction hyps as [|g rest IH]; cbn [find_s1ok]; intros H; [discriminate|].
  apply Forall_cons_iff in Hh as [Hg Hrest].
  destruct g as [id args]. destruct args as [|b [|l [|a [|m [|? ?]]]]]; try exact (IH Hrest H).
  destruct (Nat.eqb_spec id 60); [|exact (IH Hrest H)]. injection H as <- <- <- <-. subst id.
  unfold APS.gholds, GP2 in Hg. cbn [g_id g_args map Nat.eqb] in Hg. exact Hg.
Qed.

(* [comment removed for export] *)
Section RuleSound.
Variable E : env.
Variable M : mem.
Variable c : vc.
Variable kx : list kentry.
Hypothesis Hk : know_ok SEGS E M (vc_kn c).
Hypothesis Hh : Forall (APS.gholds GP2 E M) (vc_hyps c).
Hypothesis HX : know_ok SEGS E M kx.

Lemma lin_eqx_sound : forall a b, lin_eqx kx a b = true -> xt_den E a = xt_den E b.
Proof.
  intros a b H. unfold lin_eqx in H. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M kx _ _ HX H1). pose proof (lin_ge0_sound SEGS E M kx _ _ HX H2). lia.
Qed.
Lemma byte_is_sound : forall bt z, 0 <= z < two64 -> byte_is kx bt z = true -> uD E bt = z.
Proof.
  intros bt z Hz H. unfold byte_is in H. apply lin_eqx_sound in H. cbn [xt_den edenot] in H. rewrite u_lit64a in H.
  unfold two64 in Hz. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma byte_ne_sound : forall bt z, 1 <= z < two64 - 1 -> byte_ne kx bt z = true -> uD E bt <> z.
Proof.
  intros bt z Hz H. unfold byte_ne in H. unfold two64 in Hz. apply Bool.orb_prop in H as [H|H].
  - pose proof (lin_ge0_sound SEGS E M kx _ _ HX H) as A. cbn [xt_den edenot] in A. rewrite u_lit64a, Z.mod_small in A by lia. lia.
  - pose proof (lin_ge0_sound SEGS E M kx _ _ HX H) as A. cbn [xt_den edenot] in A. rewrite u_lit64a, Z.mod_small in A by lia. lia.
Qed.
Lemma lit_arg_sound : forall e z, lit_arg e = Some z -> uD E e = z mod 2 ^ 64.
Proof. intros e z H. destruct e; try discriminate. cbn in H. injection H as ->. cbn [edenot]. apply u_lit64a. Qed.

Lemma acc_goals_sound : forall hT hS L dL t' s' tb' sb',
  acc_goals kx hT hS L dL t' s' tb' sb' = true ->
  0 <= tb' < 64 /\ 0 <= sb' < 64 /\ uD E t' + tb' <= uD E L + dL + 2 /\ 3 * uD E s' <= 5 * (uD E L + dL) + sb'.
Proof.
  intros hT hS L dL t' s' tb' sb' H. unfold acc_goals in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  apply (lin_ge0_h2_sound E M kx) in H5; [|exact HX]. apply (lin_ge0_h2_sound E M kx) in H6; [|exact HX].
  cbn [xt_den] in H5, H6. rewrite !xt_den_xN in H6. cbn [Z.of_nat] in H6. lia.
Qed.

Lemma acc_hyp_sound : forall i args, acc_hyp c i = Some args -> p_acc (map (APS.uE E) args) M.
Proof.
  intros i args H. unfold acc_hyp in H. destruct (nth_error (vc_hyps c) i) as [[id as0]|] eqn:Hn; [|discriminate].
  destruct (Nat.eqb_spec id 62); [|discriminate]. injection H as <-. subst id.
  pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hn)) as G. unfold APS.gholds, GP2 in G. cbn [g_id g_args Nat.eqb] in G. exact G.
Qed.
Lemma str_hyp_sound : forall i args, str_hyp c i = Some args -> p_str (map (APS.uE E) args) M.
Proof.
  intros i args H. unfold str_hyp in H. destruct (nth_error (vc_hyps c) i) as [[id as0]|] eqn:Hn; [|discriminate].
  destruct (Nat.eqb_spec id 61); [|discriminate]. injection H as <-. subst id.
  pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hn)) as G. unfold APS.gholds, GP2 in G. cbn [g_id g_args Nat.eqb] in G. exact G.
Qed.
Lemma oc_hyp_sound : forall i args, oc_hyp c i = Some args -> p_ocinv (map (APS.uE E) args) M.
Proof.
  intros i args H. unfold oc_hyp in H. destruct (nth_error (vc_hyps c) i) as [[id as0]|] eqn:Hn; [|discriminate].
  destruct (Nat.eqb_spec id 64); [|discriminate]. injection H as <-. subst id.
  pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hn)) as G. unfold APS.gholds, GP2 in G. cbn [g_id g_args Nat.eqb] in G. exact G.
Qed.

(* [comment removed for export] *)
Lemma idx_rec_sound : forall buf len a1 n k v, p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M ->
  find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4 = Some v -> uD E k <= uD E n + 1 ->
  idxm M (uD E a1) (uD E n) (uD E len) (uD E k) = uD E (recval 4 v).
Proof.
  intros buf len a1 n k v S1 Hr Hkn.
  pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd.
  assert (Had : xt_den E (addr_idx a1 k) = uD E a1 + 4 * uD E k).
  { unfold addr_idx. cbn [xt_den]. rewrite xt_den_xN. lia. }
  rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * uD E k) 4) with (u32_at M (uD E a1 + 4 * uD E k)) in Hrd.
  pose proof (u64_range (edenot E k)).
  assert (Hk2 : 0 <= bv_unsigned (edenot E k) <= bv_unsigned (edenot E n) + 1) by lia.
  rewrite (s1ok_rec_idxm M _ _ _ _ _ _ S1 Hk2 Hrd). symmetry. pose proof (recval_sound E 4 v ltac:(lia)) as Hx.
  cbn [Z.of_nat Z.mul Pos.mul] in Hx. exact Hx.
Qed.
Lemma idx_rec1_sound : forall buf len a1 n k v, p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M ->
  find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4 = Some v -> uD E k + 1 <= uD E n + 1 ->
  idxm M (uD E a1) (uD E n) (uD E len) (uD E k + 1) = uD E (recval 4 v).
Proof.
  intros buf len a1 n k v S1 Hr Hkn.
  pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd.
  assert (Had : xt_den E (addr_idx1 a1 k) = uD E a1 + 4 * (uD E k + 1)).
  { unfold addr_idx1. cbn [xt_den]. rewrite xt_den_xN. lia. }
  rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * (uD E k + 1)) 4) with (u32_at M (uD E a1 + 4 * (uD E k + 1))) in Hrd.
  pose proof (u64_range (edenot E k)).
  assert (Hk2 : 0 <= bv_unsigned (edenot E k) + 1 <= bv_unsigned (edenot E n) + 1) by lia.
  rewrite (s1ok_rec_idxm M _ _ _ _ _ _ S1 Hk2 Hrd). symmetry. pose proof (recval_sound E 4 v ltac:(lia)) as Hx.
  cbn [Z.of_nat Z.mul Pos.mul] in Hx. exact Hx.
Qed.
Lemma idx_recj_sound : forall buf len a1 n k j v, p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M ->
  find_rec (vc_kn c) (vc_kn c) ((a1, 4 * j) :: xN 4 k) 4 = Some v -> 0 <= uD E k + j <= uD E n + 1 ->
  idxm M (uD E a1) (uD E n) (uD E len) (uD E k + j) = uD E (recval 4 v).
Proof.
  intros buf len a1 n k j v S1 Hr Hkn.
  pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd.
  assert (Had : xt_den E ((a1, 4 * j) :: xN 4 k) = uD E a1 + 4 * (uD E k + j)).
  { cbn [xt_den]. rewrite xt_den_xN. lia. }
  rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * (uD E k + j)) 4) with (u32_at M (uD E a1 + 4 * (uD E k + j))) in Hrd.
  rewrite (s1ok_rec_idxm M _ _ _ _ _ _ S1 Hkn Hrd). symmetry. pose proof (recval_sound E 4 v ltac:(lia)) as Hx.
  cbn [Z.of_nat Z.mul Pos.mul] in Hx. exact Hx.
Qed.
(* [comment removed for export] *)
Lemma byte_rec_sound : forall buf len a1 n bs x bv, p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M ->
  input M (uD E buf) (uD E len) = Some bs ->
  find_rec (vc_kn c) (vc_kn c) [(buf, 0); (x, 0)] 1 = Some bv -> uD E x < uD E len + 64 ->
  nthb bs (uD E x) = uD E (recval 1 bv).
Proof.
  intros buf len a1 n bs x bv S1 Hin Hr Hx.
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl & Hbl & _).
  pose proof (u64_range (edenot E buf)) as R1. pose proof (u64_range (edenot E x)) as R2.
  pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (x, 0)] bv ltac:(lia) Hbl Hl Hin Hk Hr) as IB.
  cbn [xt_den] in IB.
  replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E x) + 0 + 0) - bv_unsigned (edenot E buf)) with (uD E x) in IB by lia.
  apply IB. lia.
Qed.

Lemma check_acc_init_sound : forall hk ht hs g, check_acc_init c kx hk ht hs g = true -> APS.gholds GP2 E M g.
Proof.
  intros hk ht hs [id args] H. unfold check_acc_init in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|a1 [|n [|len [|k [|t [|s' [|tbe [|sbe [|? ?]]]]]]]]]; try discriminate.
  destruct (find_s1ok (vc_hyps c)) as [[[[buf len0] a10] n0]|] eqn:Hs; [|discriminate].
  destruct (lit_arg tbe) as [tb|] eqn:Htb; [|discriminate]. destruct (lit_arg sbe) as [sb|] eqn:Hsb; [|discriminate].
  apply andb_prop in H as [H HG]. apply andb_prop in H as [H HL]. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. apply expr_eqb_eq in E3. subst len0 a10 n0.
  pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
  apply (lin_ge0_h2_sound E M kx) in HL; [|exact HX]. cbn [xt_den] in HL.
  destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
  unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_acc. unfold APS.uE in *.
  rewrite (lit_arg_sound _ _ Htb), (lit_arg_sound _ _ Hsb). rewrite !Z.mod_small by lia.
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl & Hbl & Ha1 & Hn1 & bs & Hin & _).
  pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E n)) as RN.
  pose proof (idxm_ge_k M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HI.
  repeat split; lia.
Qed.

Lemma check_str_sound : forall i d g, check_str c kx i d g = true -> APS.gholds GP2 E M g.
Proof.
  intros i d [id args] H. unfold check_str in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|buf [|len [|a1 [|n [|k [|p' [|? ?]]]]]]]; try discriminate.
  destruct (str_hyp c i) as [argsh|] eqn:Hsh; [|discriminate].
  destruct argsh as [|bufh [|lenh [|a1h [|nh [|kh [|p [|? ?]]]]]]]; try discriminate.
  apply andb_prop in H as [H HB]. apply andb_prop in H as [H HP].
  apply andb_prop in H as [H E5]. apply andb_prop in H as [H E4]. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. apply expr_eqb_eq in E3. apply expr_eqb_eq in E4. apply expr_eqb_eq in E5. subst.
  apply lin_eqx_sound in HP. cbn [xt_den] in HP.
  assert (HP' : bv_unsigned (edenot E p') = bv_unsigned (edenot E p) + d) by lia. clear HP.
  pose proof (str_hyp_sound i _ Hsh) as SH. cbn [map] in SH. unfold p_str in SH. unfold APS.uE in *.
  destruct SH as (Hl & Hbl & Ha1 & Hk1 & bs & x & j & fq' & fq & Hin & Hx & H34 & Hq' & Hpj & Hjl & Hq).
  destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1) as [bv|] eqn:Hr; [|discriminate].
  all: pose proof (u64_range (edenot E buf)) as R1; pose proof (u64_range (edenot E p)) as R2; pose proof (u64_range (edenot E p')) as R3.
  all: pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (p, 0)] bv ltac:(lia) Hbl Hl Hin Hk Hr) as IB;
       cbn [xt_den] in IB;
       replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E p) + 0 + 0) - bv_unsigned (edenot E buf)) with (uD E p) in IB by lia;
       specialize (IB ltac:(lia)).
  all: unfold APS.gholds, GP2; cbn [g_id g_args map Nat.eqb]; unfold p_str; unfold APS.uE.
  all: destruct fq as [|f]; [cbn [S1M.qsearch] in Hq; discriminate|]; cbn [S1M.qsearch] in Hq; rewrite IB in Hq.
  all: destruct (Z.eqb_spec d 1) as [->|Hd1].
  1: apply andb_prop in HB as [B1 B2]; apply byte_ne_sound in B1; [|unfold two64; lia]; apply byte_ne_sound in B2; [|unfold two64; lia];
       change S1M.QUOTE with 34 in Hq; change S1M.BACKSLASH with 92 in Hq;
       destruct (Z.eqb_spec (uD E (recval 1 bv)) 34); [lia|]; destruct (Z.eqb_spec (uD E (recval 1 bv)) 92); [lia|];
       pose proof (S1M.qsearch_ge _ _ _ _ Hq) as [G1 G2];
       repeat split; try assumption; try lia;
       exists bs, x, j, fq', f; repeat split; try assumption; try lia; rewrite HP'; exact Hq.
  all: destruct (Z.eqb_spec d 2) as [->|Hd2]; [|discriminate];
       apply byte_is_sound in HB; [|unfold two64; lia];
       change S1M.QUOTE with 34 in Hq; change S1M.BACKSLASH with 92 in Hq;
       destruct (Z.eqb_spec (uD E (recval 1 bv)) 34); [lia|]; destruct (Z.eqb_spec (uD E (recval 1 bv)) 92); [|lia];
       pose proof (S1M.qsearch_ge _ _ _ _ Hq) as [G1 G2];
       repeat split; try assumption; try lia;
       exists bs, x, j, fq', f; repeat split; try assumption; try lia; rewrite HP'; exact Hq.
Qed.

Lemma check_oc_recs_sound : forall recs oc d' t' j, check_oc_recs c kx oc d' t' j recs = true -> 0 <= j ->
  forall dd, uD E d' - j - Z.of_nat (length recs) < dd <= uD E d' - j -> 0 <= uD E oc + 8 * dd ->
  exists x, u32_at M (uD E oc + 8 * dd) = Some x /\ x + 1 <= uD E t'.
Proof.
  intros recs. induction recs as [|hx rest IH]; intros oc d' t' j H Hj dd Hdd Hpos; cbn [check_oc_recs length] in H, Hdd; [lia|].
  destruct (find_rec (vc_kn c) (vc_kn c) ((oc, - (8 * j)) :: xN 8 d') 4) as [v|] eqn:Hr; [|discriminate].
  apply andb_prop in H as [HL HR].
  destruct (Z.eq_dec dd (uD E d' - j)) as [->|Hne].
  - apply (lin_ge0_h2_sound E M kx) in HL; [|exact HX]. cbn [xt_den] in HL.
    pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd. cbn [xt_den] in Hrd. rewrite xt_den_xN in Hrd.
    replace (Z.of_nat 8) with 8 in Hrd by reflexivity.
    replace (bv_unsigned (edenot E oc) + - (8 * j) + 8 * bv_unsigned (edenot E d')) with (uD E oc + 8 * (uD E d' - j)) in Hrd by lia.
    exists (uD E (recvalx kx v)). split; [|lia]. unfold u32_at. rewrite Hrd. f_equal. symmetry. apply (recvalx_sound E M kx v HX).
  - apply (IH oc d' t' (j + 1) HR ltac:(lia) dd); [rewrite Nat2Z.inj_succ in Hdd; lia | exact Hpos].
Qed.
Lemma check_oc_sound : forall src recs hd ht g, check_oc c kx src recs hd ht g = true -> APS.gholds GP2 E M g.
Proof.
  intros src recs hd ht [id args] H. unfold check_oc in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|oc [|d' [|t' [|? ?]]]]; try discriminate.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [HB HBase].
  pose proof (lin_ge0_sound SEGS E M kx _ _ HX HB) as B. cbn [xt_den edenot] in B. rewrite xt_den_xN in B.
  unfold two64 in B. replace (Z.of_nat 8) with 8 in B by reflexivity.
  pose proof (u64_range (edenot E oc)) as R1. pose proof (u64_range (edenot E d')) as R2. pose proof (u64_range (edenot E t')) as R3.
  pose proof (check_oc_recs_sound _ _ _ _ _ HR ltac:(lia)) as REC. rewrite Z.sub_0_r in REC.
  unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_ocinv. unfold APS.uE in *. unfold two64 in *.
  destruct src as [i|].
  - destruct (oc_hyp c i) as [argsh|] eqn:Ho; [|discriminate].
    destruct argsh as [|och [|d [|t [|? ?]]]]; try discriminate.
    apply andb_prop in HBase as [HBase HD]. apply andb_prop in HBase as [Eo HT]. apply expr_eqb_eq in Eo. subst och.
    apply (lin_ge0_h2_sound E M kx) in HT; [|exact HX]. cbn [xt_den] in HT.
    apply (lin_ge0_h2_sound E M kx) in HD; [|exact HX]. cbn [xt_den] in HD.
    pose proof (oc_hyp_sound i _ Ho) as OH. cbn [map] in OH. unfold p_ocinv in OH. unfold APS.uE in OH.
    destruct OH as (Hd0 & Hob & Hall).
    split; [lia|]. split; [lia|]. intros dd Hdd.
    destruct (Z.le_gt_cases dd (uD E d)) as [Hle|Hgt].
    + destruct (Hall dd ltac:(lia)) as (v & Hv & Hvt). exists v. split; [exact Hv | lia].
    + apply REC; lia.
  - apply (lin_ge0_h2_sound E M kx) in HBase; [|exact HX]. cbn [xt_den edenot] in HBase.
    rewrite u_lit64a, Z.mod_0_l in HBase by lia.
    split; [lia|]. split; [lia|]. intros dd Hdd. apply REC; lia.
Qed.

(* [comment removed for export] *)
Lemma iab_hyp_sound : forall i args, iab_hyp c i = Some args -> p_iab (map (APS.uE E) args) M.
Proof.
  intros i args H. unfold iab_hyp in H. destruct (nth_error (vc_hyps c) i) as [[id as0]|] eqn:Hn; [|discriminate].
  destruct (Nat.eqb_spec id 65); [|discriminate]. injection H as <-. subst id.
  pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hn)) as G. unfold APS.gholds, GP2 in G. cbn [g_id g_args Nat.eqb] in G. exact G.
Qed.
Lemma check_iab_recs_sound : forall recs ia d' j, check_iab_recs c kx ia d' j recs = true -> 0 <= j ->
  forall dd, uD E d' - j - Z.of_nat (length recs) < dd <= uD E d' - j -> 0 <= uD E ia + dd ->
  exists x, u8_at M (uD E ia + dd) = Some x /\ x <= 1.
Proof.
  intros recs. induction recs as [|[hl hu] rest IH]; intros ia d' j H Hj dd Hdd Hpos; cbn [check_iab_recs length] in H, Hdd; [lia|].
  destruct (find_rec (vc_kn c) (vc_kn c) ((ia, - j) :: xN 1 d') 1) as [v|] eqn:Hr; [|discriminate].
  apply andb_prop in H as [HL HR].
  destruct (Z.eq_dec dd (uD E d' - j)) as [->|Hne].
  - assert (HV : bv_unsigned (edenot E (recval 1 v)) <= 1).
    { apply Bool.orb_prop in HL. destruct HL as [HL|HL].
      - destruct v as [z| | | | | | |]; try discriminate HL. apply andb_prop in HL as [Z0 Z1]. apply Z.leb_le in Z0. apply Z.leb_le in Z1.
        rewrite (recval_sound E 1 (ELit z) ltac:(lia)). cbn [edenot]. rewrite u_lit64a.
        replace (8 * Z.of_nat 1) with 8 by reflexivity. rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite Z.mod_small by lia. exact Z1.
      - apply (lin_ge0_h2_sound E M kx) in HL; [|exact HX]. cbn [xt_den] in HL.
        change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in HL. rewrite u_lit64a in HL. change (1 mod 2 ^ 64) with 1 in HL. lia. }
    pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd. cbn [xt_den] in Hrd. rewrite xt_den_xN in Hrd.
    pose proof (recval_sound E 1 v ltac:(lia)) as RV. rewrite <- RV in Hrd.
    replace (bv_unsigned (edenot E ia) + - j + Z.of_nat 1 * bv_unsigned (edenot E d')) with (uD E ia + (uD E d' - j)) in Hrd by lia.
    exists (bv_unsigned (edenot E (recval 1 v))). split; [unfold u8_at; exact Hrd | exact HV].
  - apply (IH ia d' (j + 1) HR ltac:(lia) dd); [rewrite Nat2Z.inj_succ in Hdd; lia | exact Hpos].
Qed.
Lemma check_iab_sound : forall src recs hd g, check_iab c kx src recs hd g = true -> APS.gholds GP2 E M g.
Proof.
  intros src recs hd [id args] H. unfold check_iab in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|ia [|d' [|? ?]]]; try discriminate.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [HB HBase].
  pose proof (lin_ge0_sound SEGS E M kx _ _ HX HB) as B. cbn [xt_den edenot] in B. rewrite xt_den_xN in B.
  unfold two64 in B. replace (Z.of_nat 1) with 1 in B by reflexivity.
  pose proof (u64_range (edenot E ia)) as R1. pose proof (u64_range (edenot E d')) as R2.
  pose proof (check_iab_recs_sound _ _ _ _ HR ltac:(lia)) as REC. rewrite Z.sub_0_r in REC.
  unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_iab. unfold APS.uE in *. unfold two64 in *.
  destruct src as [i|].
  - destruct (iab_hyp c i) as [argsh|] eqn:Ho; [|discriminate].
    destruct argsh as [|iah [|d [|? ?]]]; try discriminate.
    apply andb_prop in HBase as [Eo HD]. apply expr_eqb_eq in Eo. subst iah.
    apply (lin_ge0_h2_sound E M kx) in HD; [|exact HX]. cbn [xt_den] in HD.
    pose proof (iab_hyp_sound i _ Ho) as OH. cbn [map] in OH. unfold p_iab in OH. unfold APS.uE in OH.
    destruct OH as (Hd0 & Hob & Hall).
    split; [lia|]. split; [lia|]. intros dd Hdd.
    destruct (Z.le_gt_cases dd (uD E d)) as [Hle|Hgt].
    + destruct (Hall dd ltac:(lia)) as (v & Hv & Hvt). exists v. split; [exact Hv | lia].
    + apply REC; lia.
  - apply (lin_ge0_h2_sound E M kx) in HBase; [|exact HX]. cbn [xt_den edenot] in HBase.
    rewrite u_lit64a, Z.mod_0_l in HBase by lia.
    split; [lia|]. split; [lia|]. intros dd Hdd. apply REC; lia.
Qed.

Lemma check_str_start_sound : forall hk g, check_str_start c kx hk g = true -> APS.gholds GP2 E M g.
Proof.
  intros hk [id args] H. unfold check_str_start in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|buf [|len [|a1 [|n [|k [|p [|? ?]]]]]]]; try discriminate.
  destruct (find_s1ok (vc_hyps c)) as [[[[buf0 len0] a10] n0]|] eqn:Hs; [|discriminate].
  apply andb_prop in H as [H HR]. apply andb_prop in H as [H HK2]. apply andb_prop in H as [H HK1].
  apply andb_prop in H as [H E4]. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. apply expr_eqb_eq in E3. apply expr_eqb_eq in E4. subst buf0 len0 a10 n0.
  pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
  pose proof (lin_ge0_sound SEGS E M kx _ _ HX HK1) as K1. cbn [xt_den edenot] in K1. rewrite u_lit64a, Z.mod_small in K1 by lia.
  apply (lin_ge0_h2_sound E M kx) in HK2; [|exact HX]. cbn [xt_den] in HK2.
  destruct (find_rec (vc_kn c) (vc_kn c) ((a1, -4) :: xN 4 k) 4) as [v|] eqn:Hr; [|discriminate].
  apply andb_prop in HR as [HP HB]. apply lin_eqx_sound in HP. cbn [xt_den] in HP.
  destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
  apply byte_is_sound in HB; [|unfold two64; lia].
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl & Hbl & Ha1 & Hn1 & bs & Hin & Hsucc & Hlen & Hz & Hidx & _).
  pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E n)) as RN. pose proof (u64_range (edenot E a1)) as RA.
  pose proof (u64_range (edenot E (recval 4 v))) as RX. unfold APS.uE in *.
  (* [comment removed for export] *)
  pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd. cbn [xt_den] in Hrd. rewrite xt_den_xN in Hrd.
  replace (Z.of_nat 4) with 4 in Hrd by reflexivity.
  replace (bv_unsigned (edenot E a1) + -4 + 4 * bv_unsigned (edenot E k)) with (uD E a1 + 4 * (uD E k - 1)) in Hrd by lia.
  change (rdZ M (uD E a1 + 4 * (uD E k - 1)) 4) with (u32_at M (uD E a1 + 4 * (uD E k - 1))) in Hrd.
  replace (2 ^ (8 * 4)) with (2 ^ 32) in Hrd by reflexivity. rewrite <- recval4 in Hrd.
  assert (Hk1 : 0 <= uD E k - 1 <= uD E n + 1) by lia.
  pose proof (idxm_of_rec M _ _ _ _ S1 (uD E k - 1) _ Hk1 Hrd) as HI.
  (* [comment removed for export] *)
  pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k - 1) ltac:(lia)) as HIL.
  pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v) bv S1 Hin Hb ltac:(lia)) as BY. rewrite HB in BY.
  pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k - 1) Hk1 ltac:(rewrite HI, BY; lia)) as Hkn.
  destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E k - 1) ltac:(lia) ltac:(rewrite HI, BY; reflexivity)) as (j & fq & A & B & C & D).
  rewrite HI in A, C.
  unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_str. unfold APS.uE.
  split; [lia|]. split; [exact Hbl|]. split; [exact Ha1|]. split; [lia|].
  exists bs, (uD E (recval 4 v)), j, fq, fq. split; [exact Hin|]. split; [rewrite <- Hrd; f_equal; lia|].
  split; [exact BY|]. split; [exact C|]. split; [lia|]. split; [lia|].
  replace (bv_unsigned (edenot E p)) with (bv_unsigned (edenot E (recval 4 v)) + 1) by lia. exact C.
Qed.

Lemma check_strhex_sound : forall i segs g, check_strhex c kx i segs g = true -> APS.gholds GP2 E M g.
Proof.
  intros i segs [id args] H. unfold check_strhex in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|buf [|len [|a1 [|n [|k [|p' [|? ?]]]]]]]; try discriminate.
  destruct (str_hyp c i) as [argsh|] eqn:Hsh; [|discriminate].
  destruct argsh as [|bufh [|lenh [|a1h [|nh [|kh [|p [|? ?]]]]]]]; try discriminate.
  apply andb_prop in H as [H HW].
  apply andb_prop in H as [H E5]. apply andb_prop in H as [H E4]. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. apply expr_eqb_eq in E3. apply expr_eqb_eq in E4. apply expr_eqb_eq in E5. subst.
  destruct (uhex_walk c kx buf p 0 segs) as [d'|] eqn:Hwk; [|discriminate].
  apply lin_eqx_sound in HW. cbn [xt_den] in HW.
  pose proof (str_hyp_sound i _ Hsh) as SH. cbn [map] in SH. unfold p_str in SH. unfold APS.uE in *.
  destruct SH as (Hl & Hbl & Ha1 & Hk1 & bs & x & j & fq' & fq & Hin & Hx & H34 & Hq' & Hpj & Hjl & Hq).
  pose proof (u64_range (edenot E buf)) as R1. pose proof (u64_range (edenot E p)) as R2.
  destruct (uhex_walk_sound E M c kx buf len bs j segs Hk HX ltac:(lia) Hbl Hl Hin Hjl p 0 d' ltac:(lia)
              ltac:(exists fq; rewrite Z.add_0_r; exact Hq) Hwk) as [Hd [fq2 Q2]].
  pose proof (S1M.qsearch_ge _ _ _ _ Q2) as [G1 G2].
  unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_str. unfold APS.uE.
  repeat split; try assumption; try lia.
  exists bs, x, j, fq', fq2. repeat split; try assumption; try lia.
  replace (bv_unsigned (edenot E p')) with (bv_unsigned (edenot E p) + d') by lia. exact Q2.
Qed.

(* [comment removed for export] *)
Lemma adv_xs_sound : forall buf len a1 n bs nn k j xs,
  p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M -> input M (uD E buf) (uD E len) = Some bs ->
  adv_xs c kx buf a1 k j nn = Some xs -> 0 <= j -> 0 <= uD E k + j <= uD E n + 1 ->
  length xs = nn /\
  forall i x, nth_error xs i = Some x -> uD E k + j + Z.of_nat i < uD E n /\ idxm M (uD E a1) (uD E n) (uD E len) (uD E k + j + Z.of_nat i) = uD E x.
Proof.
  intros buf len a1 n bs nn. induction nn as [|nn IH]; intros k j xs S1 Hin H Hj Hkj; cbn [adv_xs] in H.
  - injection H as <-. split; [reflexivity|]. intros [|i] x Hx; discriminate.
  - destruct (find_rec (vc_kn c) (vc_kn c) ((a1, 4 * j) :: xN 4 k) 4) as [v|] eqn:Hr; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
    destruct (lin_ge0 kx [(recval 1 bv, 0)] [(ELit 1, 0)]) eqn:HNZ; [|discriminate].
    destruct (adv_xs c kx buf a1 k (j + 1) nn) as [xs'|] eqn:Hrest; [|discriminate]. injection H as <-.
    pose proof (lin_ge0_sound SEGS E M kx _ _ HX HNZ) as NZ. cbn [xt_den edenot] in NZ. rewrite u_lit64a, Z.mod_small in NZ by lia.
    pose proof (idx_recj_sound _ _ _ _ _ _ _ S1 Hr Hkj) as HI.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k + j) ltac:(lia)) as HIL.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v) bv S1 Hin Hb ltac:(rewrite <- HI; lia)) as BY.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k + j) ltac:(lia) ltac:(rewrite HI, BY; lia)) as Hlt.
    destruct (IH k (j + 1) xs' S1 Hin Hrest ltac:(lia) ltac:(lia)) as [Hlen Hall].
    split; [cbn [length]; rewrite Hlen; reflexivity|].
    intros [|i] x Hx; cbn [nth_error] in Hx.
    + injection Hx as <-. rewrite Z.add_0_r. split; [lia | exact HI].
    + destruct (Hall i x Hx) as [A B]. rewrite Nat2Z.inj_succ.
      replace (uD E k + j + Z.succ (Z.of_nat i)) with (uD E k + (j + 1) + Z.of_nat i) by lia. split; [exact A | exact B].
Qed.
Lemma step_facts_sound : forall buf len a1 n bs k j xs,
  p_s1ok [uD E buf; uD E len; uD E a1; uD E n] M -> input M (uD E buf) (uD E len) = Some bs -> 0 <= j -> 0 <= uD E k + j ->
  (forall i x, nth_error xs i = Some x -> uD E k + j + Z.of_nat i < uD E n /\ idxm M (uD E a1) (uD E n) (uD E len) (uD E k + j + Z.of_nat i) = uD E x) ->
  know_ok SEGS E M (step_facts (hiZ (vc_kn c) len) xs).
Proof.
  intros buf len a1 n bs k j xs S1 Hin Hj Hkj. revert j Hj Hkj. induction xs as [|x1 rest IH]; intros j Hj Hkj Hall; cbn [step_facts]; [constructor|].
  destruct rest as [|x2 rest']; [constructor|].
  constructor.
  - destruct (Hall 0%nat x1 eq_refl) as [A1l B1]. destruct (Hall 1%nat x2 eq_refl) as [A2 B2].
    cbn [Z.of_nat] in A1l, B1. rewrite Z.add_0_r in A1l, B1. change (Z.of_nat 1) with 1 in A2, B2.
    pose proof (idxm_step M _ _ _ _ bs S1 Hin (uD E k + j) ltac:(lia)) as ST. rewrite B1 in ST.
    replace (uD E k + j + 1) with (uD E k + j + 1) in ST by lia. rewrite B2 in ST.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k + j + 1) ltac:(lia)) as HIL. rewrite B2 in HIL.
    pose proof (u64_range (edenot E x1)) as R1. pose proof (u64_range (edenot E x2)) as R2.
    pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
    apply (fact_sub E M x2 x1 (uD E x2) (uD E x1)); try apply u_mod_self; lia.
  - apply (IH (j + 1)); [lia | lia |]. intros i x Hx. destruct (Hall (S i) x Hx) as [A B].
    rewrite Nat2Z.inj_succ in A, B. replace (uD E k + j + Z.succ (Z.of_nat i)) with (uD E k + (j + 1) + Z.of_nat i) in A, B by lia.
    split; [exact A | exact B].
Qed.
Lemma check_acc_sound : forall i m hT hS g, check_acc c kx i m hT hS g = true -> APS.gholds GP2 E M g.
Proof.
  intros i m hT hS [id args] H. unfold check_acc in H. cbn [g_id g_args] in H.
  apply andb_prop in H as [Hid H]. apply Nat.eqb_eq in Hid. subst id.
  destruct args as [|a1 [|n [|len [|k' [|t' [|s' [|tbe' [|sbe' [|? ?]]]]]]]]]; try discriminate.
  destruct (acc_hyp c i) as [argsh|] eqn:Hah; [|discriminate].
  destruct argsh as [|a1h [|nh [|lenh [|k [|t [|s0 [|tbe [|sbe [|? ?]]]]]]]]]; try discriminate.
  destruct (find_s1ok (vc_hyps c)) as [[[[buf len0] a10] n0]|] eqn:Hs; [|discriminate].
  destruct (lit_arg tbe') as [tb'|] eqn:Htb'; [|discriminate]. destruct (lit_arg sbe') as [sb'|] eqn:Hsb'; [|discriminate].
  destruct (lit_arg tbe) as [tb|] eqn:Htb; [|discriminate]. destruct (lit_arg sbe) as [sb|] eqn:Hsb; [|discriminate].
  apply andb_prop in H as [H HM].
  apply andb_prop in H as [H E6]. apply andb_prop in H as [H E5]. apply andb_prop in H as [H E4].
  apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. apply expr_eqb_eq in E3. apply expr_eqb_eq in E4. apply expr_eqb_eq in E5. apply expr_eqb_eq in E6.
  subst a1h nh lenh len0 a10 n0.
  pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
  pose proof (acc_hyp_sound i _ Hah) as AH. cbn [map] in AH. unfold p_acc in AH. unfold APS.uE in *.
  rewrite (lit_arg_sound _ _ Htb), (lit_arg_sound _ _ Hsb) in AH.
  destruct AH as (Hn0 & Ha1 & Hkn & Ht & Hs0).
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl & Hbl & _ & Hn1 & bs & Hin & _).
  pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E k')) as RK'. pose proof (u64_range (edenot E n)) as RN.
  pose proof (u64_range (edenot E t)) as RT. pose proof (u64_range (edenot E s0)) as RS.
  set (I := idxm M (uD E a1) (uD E n) (uD E len)) in *.
  (* [comment removed for export] *)
  assert (GOAL : forall tb1 sb1 L, 0 <= tb1 < 64 -> 0 <= sb1 < 64 -> tb' = tb1 -> sb' = sb1 ->
            uD E k' <= uD E n + 1 -> L <= I (uD E k') ->
            uD E t' + tb1 <= L + 2 -> 3 * uD E s' <= 5 * L + sb1 ->
            APS.gholds GP2 E M (GA 62 [a1; n; len; k'; t'; s'; tbe'; sbe'])).
  { intros tb1 sb1 L Htb1 Hsb1 -> -> HK HL HT HS. unfold APS.gholds, GP2. cbn [g_id g_args map Nat.eqb]. unfold p_acc. unfold APS.uE.
    rewrite (lit_arg_sound _ _ Htb'), (lit_arg_sound _ _ Hsb'). rewrite !Z.mod_small by lia.
    fold I. repeat split; lia. }
  destruct m as [| | | |istr| | |nn str].
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HKK HG]. apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v|] eqn:Hr; [|discriminate].
    destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
    pose proof (idx_rec_sound _ _ _ _ _ _ S1 Hr ltac:(lia)) as HI. fold I in HI.
    apply (GOAL tb' sb' (uD E (recval 4 v))); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k)) by lia; rewrite HI; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HM GS]. apply andb_prop in HM as [HM GT].
    apply andb_prop in HM as [HM B8]. apply andb_prop in HM as [HM B7]. apply andb_prop in HM as [HM B6]. apply andb_prop in HM as [HM B5].
    apply andb_prop in HM as [HM B4]. apply andb_prop in HM as [HM B3]. apply andb_prop in HM as [HM B2]. apply andb_prop in HM as [HKK B1].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.ltb_lt in B4.
    apply Z.leb_le in B5. apply Z.ltb_lt in B6. apply Z.leb_le in B7. apply Z.ltb_lt in B8.
    rewrite !Z.mod_small in Ht by lia. rewrite !Z.mod_small in Hs0 by lia.
    apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    apply (lin_ge0_h2_sound E M kx) in GT; [|exact HX]. apply (lin_ge0_h2_sound E M kx) in GS; [|exact HX].
    cbn [xt_den] in GT, GS. rewrite !xt_den_xN in GS.
    replace (Z.of_nat 2) with 2 in GS by reflexivity. replace (Z.of_nat 3) with 3 in GS by reflexivity.
    apply (GOAL tb' sb' (I (uD E k))); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k)) by lia; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HKK HM]. apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v|] eqn:Hr; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
    apply andb_prop in HM as [HNZ HG].
    pose proof (lin_ge0_sound SEGS E M kx _ _ HX HNZ) as NZ. cbn [xt_den edenot] in NZ. rewrite u_lit64a, Z.mod_small in NZ by lia.
    destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
    pose proof (idx_rec_sound _ _ _ _ _ _ S1 Hr ltac:(lia)) as HI. fold I in HI.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HIL. fold I in HIL.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v) bv S1 Hin Hb ltac:(rewrite <- HI; lia)) as BY.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(fold I; rewrite HI, BY; lia)) as Hkn2.
    pose proof (idxm_step M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as ST. fold I in ST.
    apply (GOAL tb' sb' (uD E (recval 4 v) + 1)); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + 1) by lia; rewrite <- HI; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HKK HM]. apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v|] eqn:Hr; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
    apply andb_prop in HM as [HQ HG]. apply byte_is_sound in HQ; [|unfold two64; lia].
    destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
    pose proof (idx_rec_sound _ _ _ _ _ _ S1 Hr ltac:(lia)) as HI. fold I in HI.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HIL. fold I in HIL.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v) bv S1 Hin Hb ltac:(rewrite <- HI; lia)) as BY. rewrite HQ in BY.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(fold I; rewrite HI, BY; lia)) as Hkn2.
    destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(fold I; rewrite HI, BY; reflexivity)) as (j & fq & A & B & C & D).
    fold I in A, D.
    apply (GOAL tb' sb' (uD E (recval 4 v) + 2)); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + 1) by lia; rewrite <- HI; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HM HB2]. apply andb_prop in HM as [HM GT].
    apply andb_prop in HM as [HM B8]. apply andb_prop in HM as [HM B7]. apply andb_prop in HM as [HM B6]. apply andb_prop in HM as [HM B5].
    apply andb_prop in HM as [HM B4]. apply andb_prop in HM as [HM B3]. apply andb_prop in HM as [HM B2]. apply andb_prop in HM as [HKK B1].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.ltb_lt in B4.
    apply Z.leb_le in B5. apply Z.ltb_lt in B6. apply Z.leb_le in B7. apply Z.ltb_lt in B8.
    rewrite !Z.mod_small in Ht by lia. rewrite !Z.mod_small in Hs0 by lia.
    apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    apply (lin_ge0_h2_sound E M kx) in GT; [|exact HX]. cbn [xt_den] in GT.
    destruct (str_hyp c istr) as [argss|] eqn:Hst; [|discriminate].
    destruct argss as [|bufs [|lens [|a1s [|ns [|ks [|p [|? ?]]]]]]]; try discriminate.
    apply andb_prop in HB2 as [HM2 HB2]. apply andb_prop in HM2 as [HM2 HKS].
    apply andb_prop in HM2 as [HM2 F4]. apply andb_prop in HM2 as [HM2 F3]. apply andb_prop in HM2 as [F1 F2].
    apply expr_eqb_eq in F1. apply expr_eqb_eq in F2. apply expr_eqb_eq in F3. apply expr_eqb_eq in F4. subst bufs lens a1s ns.
    apply lin_eqx_sound in HKS. cbn [xt_den] in HKS.
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
    apply andb_prop in HB2 as [HQ GS]. apply byte_is_sound in HQ; [|unfold two64; lia].
    apply (lin_ge0_h2_sound E M kx) in GS; [|exact HX]. cbn [xt_den] in GS. rewrite !xt_den_xN in GS.
    replace (Z.of_nat 4) with 4 in GS by reflexivity. replace (Z.of_nat 3) with 3 in GS by reflexivity.
    pose proof (str_hyp_sound istr _ Hst) as SH. cbn [map] in SH. unfold p_str in SH. unfold APS.uE in SH.
    destruct SH as (_ & _ & _ & Hks & bs' & x & j & fq' & fq & Hin' & Hx & H34 & Hq' & Hpj & Hjl & Hq).
    rewrite Hin in Hin'. injection Hin' as <-.
    pose proof (u64_range (edenot E p)) as RP. pose proof (u64_range (edenot E ks)) as RKS.
    pose proof (byte_rec_sound _ _ _ _ bs p bv S1 Hin Hb ltac:(lia)) as BY. rewrite HQ in BY.
    pose proof (qsearch_at_quote _ _ _ _ Hq ltac:(exact BY)) as ->.
    (* [comment removed for export] *)
    assert (Hk1 : 0 <= uD E ks - 1 <= uD E n + 1) by lia.
    pose proof (idxm_of_rec M _ _ _ _ S1 (uD E ks - 1) x Hk1 ltac:(replace (uD E a1 + 4 * (uD E ks - 1)) with (bv_unsigned (edenot E a1) + 4 * (bv_unsigned (edenot E ks) - 1)) by reflexivity; exact Hx)) as HI0.
    destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E ks - 1) ltac:(lia) ltac:(rewrite HI0; exact H34)) as (j2 & fq2 & A & B & C & D).
    rewrite HI0 in C. pose proof (qsearch_det _ _ _ _ _ _ Hq' C) as <-.
    replace (uD E ks - 1 + 1) with (uD E ks) in D by lia. fold I in D.
    apply (GOAL tb' sb' (I (uD E k))); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k)) by lia; try lia.
    all: replace (bv_unsigned (edenot E ks)) with (bv_unsigned (edenot E k)) in D by lia; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HKK HM]. apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v1|] eqn:Hr1; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4) as [v2|] eqn:Hr2; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v1, 0)] 1) as [b1|] eqn:Hb1; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v2, 0)] 1) as [b2|] eqn:Hb2; [|discriminate].
    apply andb_prop in HM as [HM HG]. apply andb_prop in HM as [HN1 HN2].
    pose proof (lin_ge0_sound SEGS E M kx _ _ HX HN1) as N1. cbn [xt_den edenot] in N1. rewrite u_lit64a, Z.mod_small in N1 by lia.
    pose proof (lin_ge0_sound SEGS E M kx _ _ HX HN2) as N2. cbn [xt_den edenot] in N2. rewrite u_lit64a, Z.mod_small in N2 by lia.
    destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
    pose proof (idx_rec_sound _ _ _ _ _ _ S1 Hr1 ltac:(lia)) as HI1. fold I in HI1.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HIL1. fold I in HIL1.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v1) b1 S1 Hin Hb1 ltac:(rewrite <- HI1; lia)) as BY1.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(fold I; rewrite HI1, BY1; lia)) as Hkn1.
    pose proof (idx_rec1_sound _ _ _ _ _ _ S1 Hr2 ltac:(lia)) as HI2. fold I in HI2.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia)) as HIL2. fold I in HIL2.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v2) b2 S1 Hin Hb2 ltac:(rewrite <- HI2; lia)) as BY2.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia) ltac:(fold I; rewrite HI2, BY2; lia)) as Hkn2.
    pose proof (idxm_step M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia)) as ST. fold I in ST.
    replace (uD E k + 1 + 1) with (uD E k + 2) in ST by lia.
    apply (GOAL tb' sb' (uD E (recval 4 v2) + 1)); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + 2) by lia; rewrite <- HI2; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HKK HM]. apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v1|] eqn:Hr1; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 k) 4) as [v2|] eqn:Hr2; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v1, 0)] 1) as [b1|] eqn:Hb1; [|discriminate].
    destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v2, 0)] 1) as [b2|] eqn:Hb2; [|discriminate].
    apply andb_prop in HM as [HM HG]. apply andb_prop in HM as [HN1 HQ].
    pose proof (lin_ge0_sound SEGS E M kx _ _ HX HN1) as N1. cbn [xt_den edenot] in N1. rewrite u_lit64a, Z.mod_small in N1 by lia.
    apply byte_is_sound in HQ; [|unfold two64; lia].
    destruct (acc_goals_sound _ _ _ _ _ _ _ _ HG) as (R1 & R2 & R3 & R4).
    pose proof (idx_rec_sound _ _ _ _ _ _ S1 Hr1 ltac:(lia)) as HI1. fold I in HI1.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HIL1. fold I in HIL1.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v1) b1 S1 Hin Hb1 ltac:(rewrite <- HI1; lia)) as BY1.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(fold I; rewrite HI1, BY1; lia)) as Hkn1.
    pose proof (idx_rec1_sound _ _ _ _ _ _ S1 Hr2 ltac:(lia)) as HI2. fold I in HI2.
    pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia)) as HIL2. fold I in HIL2.
    pose proof (byte_rec_sound _ _ _ _ bs (recval 4 v2) b2 S1 Hin Hb2 ltac:(rewrite <- HI2; lia)) as BY2. rewrite HQ in BY2.
    pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia) ltac:(fold I; rewrite HI2, BY2; lia)) as Hkn2.
    destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E k + 1) ltac:(lia) ltac:(fold I; rewrite HI2, BY2; reflexivity)) as (j & fq & A & B & C & D).
    fold I in A, D. replace (uD E k + 1 + 1) with (uD E k + 2) in D by lia.
    apply (GOAL tb' sb' (uD E (recval 4 v2) + 2)); try lia.
    all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + 2) by lia; rewrite <- HI2; lia.
  - (* [comment removed for export] *)
    apply andb_prop in HM as [HM HB]. apply andb_prop in HM as [Hnn HKK]. apply Nat.ltb_lt in Hnn.
    apply lin_eqx_sound in HKK. cbn [xt_den] in HKK.
    destruct (adv_xs c kx buf a1 k 0 nn) as [xs|] eqn:Ha; [|discriminate].
    apply andb_prop in HB as [HS34 HG].
    destruct (adv_xs_sound _ _ _ _ bs nn k 0 xs S1 Hin Ha ltac:(lia) ltac:(lia)) as [Hlen Hall].
    assert (HX2 : know_ok SEGS E M (kx ++ step_facts (hiZ (vc_kn c) len) xs)).
    { apply Forall_app. split; [exact HX|]. eapply (step_facts_sound _ _ _ _ bs k 0 xs S1 Hin); [lia | lia | exact Hall]. }
    (* [comment removed for export] *)
    destruct (nth_error xs (nn - 1)) as [xl|] eqn:Hxl.
    2: { exfalso. apply nth_error_None in Hxl. lia. }
    assert (HLAST : nth (nn - 1) xs (ELit 0) = xl) by (apply nth_error_nth; exact Hxl).
    rewrite HLAST in HS34, HG.
    destruct (Hall (nn - 1)%nat xl Hxl) as [Hlt HI]. rewrite Z.add_0_r in Hlt, HI.
    replace (Z.of_nat (nn - 1)) with (Z.of_nat nn - 1) in Hlt, HI by lia.
    unfold acc_goals in HG.
    apply andb_prop in HG as [HG G6]. apply andb_prop in HG as [HG G5]. apply andb_prop in HG as [HG G4].
    apply andb_prop in HG as [HG G3]. apply andb_prop in HG as [G1 G2].
    apply Z.leb_le in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. apply Z.ltb_lt in G4.
    apply (lin_ge0_h2_sound E M _) in G5; [|exact HX2]. apply (lin_ge0_h2_sound E M _) in G6; [|exact HX2].
    cbn [xt_den] in G5, G6. rewrite !xt_den_xN in G6. cbn [Z.of_nat] in G6.
    pose proof (idxm_step M _ _ _ _ bs S1 Hin (uD E k + (Z.of_nat nn - 1)) ltac:(lia)) as ST.
    replace (uD E k + (Z.of_nat nn - 1) + 1) with (uD E k + Z.of_nat nn) in ST by lia. fold I in ST, HI.
    destruct str.
    + destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (xl, 0)] 1) as [bv|] eqn:Hb; [|discriminate].
      apply byte_is_sound in HS34; [|unfold two64; lia].
      pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k + (Z.of_nat nn - 1)) ltac:(lia)) as HIL. fold I in HIL.
      pose proof (byte_rec_sound _ _ _ _ bs xl bv S1 Hin Hb ltac:(rewrite <- HI; lia)) as BY. rewrite HS34 in BY.
      destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E k + (Z.of_nat nn - 1)) ltac:(lia) ltac:(fold I; rewrite HI, BY; reflexivity)) as (jq & fq & A & B & C & D).
      fold I in A, D. replace (uD E k + (Z.of_nat nn - 1) + 1) with (uD E k + Z.of_nat nn) in D by lia.
      apply (GOAL tb' sb' (uD E xl + 2)); try lia.
      all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + Z.of_nat nn) by lia; rewrite <- HI; lia.
    + apply (GOAL tb' sb' (uD E xl + 1)); try lia.
      all: replace (bv_unsigned (edenot E k')) with (bv_unsigned (edenot E k) + Z.of_nat nn) by lia; rewrite <- HI; lia.
Qed.
End RuleSound.

(* [comment removed for export] *)
Lemma extra_fact_sound : forall E M c kx x, know_ok SEGS E M (vc_kn c) -> Forall (APS.gholds GP2 E M) (vc_hyps c) ->
  know_ok SEGS E M kx -> kentry_ok SEGS E M (extra_fact c kx x).
Proof.
  intros E M c kx x Hk Hh Hkx. pose proof (KTriv_ok E M) as T. destruct x as [k h|k h|i hal hau hbl hbu|i d|i segs|sk sh|oi od oh|xn xe xhl xhu|bi bd bhl bhu]; cbn [extra_fact].
  9: { (* [comment removed for export] *)
       destruct (nth_error (vc_hyps c) bi) as [[id args]|] eqn:Hi; [|exact T].
       destruct args as [|ia [|dd [|? ?]]]; try exact T.
       destruct (Nat.eqb_spec id 65); [|exact T]. subst id.
       destruct (find_rec (vc_kn c) (vc_kn c) ((ia, 0) :: xN 1 bd) 1) as [v|] eqn:Hr; [|exact T].
       destruct (lin_ge0_h2 kx bhl (xN 1 bd) [(ELit 1, 0)]) eqn:Hl; [|exact T].
       destruct (lin_ge0_h2 kx bhu [(dd, 0)] [(bd, 0)]) eqn:Hu; [|exact T]. cbn [andb].
       apply (lin_ge0_h2_sound E M kx) in Hl; [|exact Hkx]. cbn [xt_den edenot] in Hl. rewrite xt_den_xN, u_lit64a in Hl.
       apply (lin_ge0_h2_sound E M kx) in Hu; [|exact Hkx]. cbn [xt_den] in Hu.
       pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hi)) as IH0. unfold APS.gholds, GP2 in IH0. cbn [g_id g_args map Nat.eqb] in IH0.
       unfold p_iab in IH0. unfold APS.uE in IH0. destruct IH0 as (Hd0 & Hnw & HALL).
       pose proof (u64_range (edenot E bd)) as R1. pose proof (u64_range (edenot E ia)) as R0.
       change (1 mod 2 ^ 64) with 1 in Hl. replace (Z.of_nat 1) with 1 in Hl by reflexivity.
       destruct (HALL (uD E bd) ltac:(lia)) as (v0 & Hv0 & Hle).
       pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd. cbn [xt_den] in Hrd. rewrite xt_den_xN in Hrd.
       pose proof (recval_sound E 1 v ltac:(lia)) as RV. rewrite <- RV in Hrd.
       replace (bv_unsigned (edenot E ia) + 0 + Z.of_nat 1 * bv_unsigned (edenot E bd)) with (uD E ia + uD E bd) in Hrd by lia.
       change (rdZ M (uD E ia + uD E bd) 1) with (u8_at M (uD E ia + uD E bd)) in Hrd.
       rewrite Hv0 in Hrd. injection Hrd as Hv.
       change (bv_unsigned (ext_val false 0 1 (edenot E v))) with (bv_unsigned (edenot E (recval 1 v))) in Hv.
       pose proof (u64_range (edenot E (recval 1 v))) as R3. unfold two64 in *.
       apply (krange_of_modeq E M (recval 1 v) (bv_unsigned (edenot E (recval 1 v)))); try lia.
       symmetry. apply Z.mod_small. lia. }
  8: { (* [comment removed for export] *)
       destruct (lin_lo_h kx xhl (fst (lin_of xe)) (snd (lin_of xe))) as [l|] eqn:H1; [|exact T].
       destruct (lin_hi_h kx xhu (fst (lin_of xe)) (snd (lin_of xe))) as [u|] eqn:H2; [|exact T].
       match goal with |- kentry_ok _ _ _ (if ?cnd then _ else _) => destruct cnd eqn:Hc; [|exact T] end.
       apply andb_prop in Hc as [Hc C4]. apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
       apply Nat.ltb_lt in C1. apply Nat.leb_le in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4.
       apply (lin_lo_h_sound E M kx) in H1; [|exact Hkx]. apply (lin_hi_h_sound E M kx) in H2; [|exact Hkx].
       pose proof (lin_of_sound E xe) as [q Hq]. unfold lden, uE in Hq.
       pose proof (u64_range (edenot E xe)) as Re.
       assert (P8 : 2 ^ (8 * Z.of_nat xn) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
       assert (q = 0) by nia. subst q.
       assert (HX : uD E (EExt false 0 xn xe) = uD E xe).
       { cbn [edenot]. unfold ext_val, ext_Z. rewrite u_lit64a.
         replace (bv_unsigned (edenot E xe) / 2 ^ (8 * Z.of_nat 0)) with (bv_unsigned (edenot E xe)) by (cbn; rewrite Z.div_1_r; reflexivity).
         rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat xn))) by lia. apply Z.mod_small. lia. }
       apply (fact_sub E M (EExt false 0 xn xe) xe (uD E xe) (uD E xe)); try lia.
       - rewrite HX. apply u_mod_self.
       - apply u_mod_self. }
  7: { (* [comment removed for export] *)
       destruct (nth_error (vc_hyps c) oi) as [[id args]|] eqn:Hi; [|exact T].
       destruct args as [|oc [|dd [|t [|? ?]]]]; try exact T.
       destruct (Nat.eqb_spec id 64); [|exact T]. subst id.
       destruct (find_rec (vc_kn c) (vc_kn c) ((oc, 0) :: xN 8 od) 4) as [v|] eqn:Hr; [|exact T].
       destruct (lin_ge0_h2 kx oh [(dd, 0)] [(od, 0)]) eqn:Hl; [|exact T].
       apply (lin_ge0_h2_sound E M kx) in Hl; [|exact Hkx]. cbn [xt_den] in Hl.
       pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hi)) as OH. unfold APS.gholds, GP2 in OH. cbn [g_id g_args map Nat.eqb] in OH.
       unfold p_ocinv in OH. unfold APS.uE in OH. destruct OH as (Hd0 & Hnw & HALL).
       pose proof (u64_range (edenot E od)) as R1. pose proof (u64_range (edenot E t)) as R2.
       destruct (HALL (uD E od) ltac:(lia)) as (v0 & Hv0 & Hle).
       pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd. cbn [xt_den] in Hrd. rewrite xt_den_xN in Hrd.
       replace (bv_unsigned (edenot E oc) + 0 + Z.of_nat 8 * bv_unsigned (edenot E od)) with (uD E oc + 8 * uD E od) in Hrd by lia.
       change (rdZ M (uD E oc + 8 * uD E od) 4) with (u32_at M (uD E oc + 8 * uD E od)) in Hrd.
       rewrite Hv0 in Hrd. injection Hrd as Hv. cbn [Z.of_nat Z.mul Pos.mul] in Hv.
       pose proof (recvalx_sound E M kx v Hkx) as RXv. pose proof (u64_range (edenot E (recvalx kx v))) as R3.
       pose proof (hiZ_sound E M (vc_kn c) t Hk) as HT.
       pose proof (Z.mod_pos_bound (bv_unsigned (edenot E v)) (2 ^ 32) ltac:(lia)) as MB.
       assert (E1 : bv_unsigned (edenot E (recvalx kx v)) = v0) by (rewrite RXv; rewrite Hv; reflexivity).
       apply (fact_sub E M t (recvalx kx v) (uD E t) (uD E (recvalx kx v))); try apply u_mod_self.
       + idtac "G1". lia.
       + idtac "G2". rewrite E1. lia.
       + idtac "G3". lia. }
  6: { (* [comment removed for export] *)
       destruct (find_s1ok (vc_hyps c)) as [[[[buf len] a1] n]|] eqn:Hs; [|exact T].
       destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 sk) 4) as [v1|] eqn:Hr1; [|exact T].
       destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx1 a1 sk) 4) as [v2|] eqn:Hr2; [|exact T].
       destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v1, 0)] 1) as [b1|] eqn:Hb1; [|exact T].
       match goal with |- kentry_ok _ _ _ (if ?cnd then _ else _) => destruct cnd eqn:Hc; [|exact T] end.
       apply andb_prop in Hc as [HNZ Hl].
       pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
       apply (lin_ge0_h2_sound E M kx) in Hl; [|exact Hkx]. cbn [xt_den] in Hl.
       pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx HNZ) as NZ. cbn [xt_den edenot] in NZ. rewrite u_lit64a, Z.mod_small in NZ by lia.
       assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl0 & Hbl & Ha1 & Hn1 & bs & Hin & _).
       pose proof (u64_range (edenot E sk)) as RK. pose proof (u64_range (edenot E n)) as RN.
       pose proof (idx_rec_sound E M c Hk buf len a1 n sk v1 S1 Hr1 ltac:(lia)) as HI1.
       pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E sk) ltac:(lia)) as HIL1.
       pose proof (byte_rec_sound E M c Hk buf len a1 n bs (recval 4 v1) b1 S1 Hin Hb1 ltac:(rewrite <- HI1; lia)) as BY1.
       pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E sk) ltac:(lia) ltac:(rewrite HI1, BY1; lia)) as Hkn1.
       pose proof (idx_rec1_sound E M c Hk buf len a1 n sk v2 S1 Hr2 ltac:(lia)) as HI2.
       pose proof (idxm_step M _ _ _ _ bs S1 Hin (uD E sk) ltac:(lia)) as ST. rewrite HI1, HI2 in ST.
       pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E sk + 1) ltac:(lia)) as HIL2. rewrite HI2 in HIL2.
       pose proof (u64_range (edenot E (recval 4 v1))) as R1. pose proof (u64_range (edenot E (recval 4 v2))) as R2.
       pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
       apply (fact_sub E M (recval 4 v2) (recval 4 v1) (uD E (recval 4 v2)) (uD E (recval 4 v1))); try apply u_mod_self; lia. }
  5: { destruct (nth_error (vc_hyps c) i) as [[id args]|] eqn:Hi; [|exact T].
       destruct args as [|buf [|len [|a1 [|n [|k [|p [|? ?]]]]]]]; try exact T.
       destruct (Nat.eqb_spec id 61); [|exact T]. subst id.
       destruct (uhex_walk c kx buf p 0 segs) as [d'|] eqn:Hw; [|exact T].
       pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hi)) as SH. unfold APS.gholds, GP2 in SH. cbn [g_id g_args map Nat.eqb] in SH.
       unfold p_str in SH. unfold APS.uE in SH.
       destruct SH as (Hl & Hbl & Ha1 & Hk1 & bs & x & j & fq' & fq & Hin & Hx & H34 & Hq' & Hpj & Hjl & Hq).
       pose proof (u64_range (edenot E buf)) as R1. pose proof (u64_range (edenot E p)) as R2.
       destruct (uhex_walk_sound E M c kx buf len bs j segs Hk Hkx ltac:(lia) Hbl Hl Hin Hjl p 0 d' ltac:(lia)
                   ltac:(exists fq; rewrite Z.add_0_r; exact Hq) Hw) as [Hd [fq2 Q2]].
       pose proof (S1M.qsearch_ge _ _ _ _ Q2) as [G1 G2].
       pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
       apply (fact_sub E M len p (uD E len) (uD E p)); try apply u_mod_self; lia. }
  4: { destruct (nth_error (vc_hyps c) i) as [[id args]|] eqn:Hi; [|exact T].
       destruct args as [|buf [|len [|a1 [|n [|k [|p [|? ?]]]]]]]; try exact T.
       destruct (Nat.eqb_spec id 61); [|exact T]. subst id.
       destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (p, 0)] 1) as [bv|] eqn:Hr; [|exact T].
       destruct (step_ok kx (recval 1 bv) d) eqn:Hs; [|exact T].
       pose proof (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hi)) as SH. unfold APS.gholds, GP2 in SH. cbn [g_id g_args map Nat.eqb] in SH.
       unfold p_str in SH. unfold APS.uE in SH.
       destruct SH as (Hl & Hbl & Ha1 & Hk1 & bs & x & j & fq' & fq & Hin & Hx & H34 & Hq' & Hpj & Hjl & Hq).
       pose proof (u64_range (edenot E buf)) as R1. pose proof (u64_range (edenot E p)) as R2.
       pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (p, 0)] bv ltac:(lia) Hbl Hl Hin Hk Hr) as IB.
       cbn [xt_den] in IB.
       replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E p) + 0 + 0) - bv_unsigned (edenot E buf)) with (uD E p) in IB by lia.
       specialize (IB ltac:(lia)).
       destruct fq as [|f]; [cbn [S1M.qsearch] in Hq; discriminate|]. cbn [S1M.qsearch] in Hq. rewrite IB in Hq.
       change S1M.QUOTE with 34 in Hq. change S1M.BACKSLASH with 92 in Hq.
       pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
       unfold step_ok in Hs.
       assert (NE : forall cc, 1 <= cc < two64 - 1 ->
                 (lin_ge0 kx [(ELit (cc - 1), 0)] [(recval 1 bv, 0)] || lin_ge0 kx [(recval 1 bv, 0)] [(ELit (cc + 1), 0)])%bool = true ->
                 uD E (recval 1 bv) <> cc).
       { intros cc Hcc Hb. unfold two64 in Hcc. apply Bool.orb_prop in Hb as [Hb|Hb];
           pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx Hb) as A; cbn [xt_den edenot] in A; rewrite u_lit64a, Z.mod_small in A by lia; lia. }
       assert (IS : forall cc, 0 <= cc < two64 ->
                 (lin_ge0 kx [(recval 1 bv, 0)] [(ELit cc, 0)] && lin_ge0 kx [(ELit cc, 0)] [(recval 1 bv, 0)])%bool = true ->
                 uD E (recval 1 bv) = cc).
       { intros cc Hcc Hb. unfold two64 in Hcc. apply andb_prop in Hb as [B1 B2].
         pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B1) as A1. pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B2) as A2.
         cbn [xt_den edenot] in A1, A2. rewrite u_lit64a, Z.mod_small in A1, A2 by lia. lia. }
       destruct (Z.eqb_spec d 1) as [->|Hd1].
       { apply andb_prop in Hs as [S1 S2]. apply NE in S1; [|unfold two64; lia]. apply NE in S2; [|unfold two64; lia].
         destruct (Z.eqb_spec (uD E (recval 1 bv)) 34); [lia|]. destruct (Z.eqb_spec (uD E (recval 1 bv)) 92); [lia|].
         pose proof (S1M.qsearch_ge _ _ _ _ Hq) as [G1 G2].
         apply (fact_sub E M len p (uD E len) (uD E p)); try apply u_mod_self; lia. }
       destruct (Z.eqb_spec d 2) as [->|Hd2]; [|discriminate].
       apply IS in Hs; [|unfold two64; lia].
       destruct (Z.eqb_spec (uD E (recval 1 bv)) 34); [lia|]. destruct (Z.eqb_spec (uD E (recval 1 bv)) 92); [|lia].
       pose proof (S1M.qsearch_ge _ _ _ _ Hq) as [G1 G2].
       apply (fact_sub E M len p (uD E len) (uD E p)); try apply u_mod_self; lia. }
  3: { destruct (nth_error (vc_kn c) i) as [K|] eqn:Hi; [|exact T].
       destruct K as [| | | | |e v v'| | | |]; try exact T. destruct e as [| |op a b| | | | |]; try exact T. destruct op; try exact T.
       destruct (lin_lo_h kx hal (fst (lin_of a)) (snd (lin_of a))) as [la|] eqn:H1; [|exact T].
       destruct (lin_hi_h kx hau (fst (lin_of a)) (snd (lin_of a))) as [ua|] eqn:H2; [|exact T].
       destruct (lin_lo_h kx hbl (fst (lin_of b)) (snd (lin_of b))) as [lb|] eqn:H3; [|exact T].
       destruct (lin_hi_h kx hbu (fst (lin_of b)) (snd (lin_of b))) as [ub|] eqn:H4; [|exact T].
       match goal with |- kentry_ok _ _ _ (if ?cnd then _ else _) => destruct cnd eqn:Hc; [|exact T] end.
       apply andb_prop in Hc as [Hc C4]. apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
       apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4. unfold two64 in C2, C4.
       apply (lin_lo_h_sound E M kx) in H1; [|exact Hkx]. apply (lin_hi_h_sound E M kx) in H2; [|exact Hkx].
       apply (lin_lo_h_sound E M kx) in H3; [|exact Hkx]. apply (lin_hi_h_sound E M kx) in H4; [|exact Hkx].
       pose proof (lin_of_sound E a) as [qa Hqa]. pose proof (lin_of_sound E b) as [qb Hqb]. unfold lden, uE in Hqa, Hqb.
       pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
       assert (qa = 0) by nia. assert (qb = 0) by nia. subst qa qb.
       assert (HK : kentry_ok SEGS E M (KRange (EAlu ALU_SLTU a b) v v')).
       { apply (proj1 (Forall_forall _ _) Hk). eapply nth_error_In. exact Hi. }
       cbn [kentry_ok edenot] in HK. rewrite u_sltu64 in HK.
       destruct (Z.eqb v 0 && Z.eqb v' 0)%bool eqn:Hv.
       { apply andb_prop in Hv as [V1 V2]. apply Z.eqb_eq in V1. apply Z.eqb_eq in V2. subst v v'.
         destruct (Z.ltb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))); [lia|].
         apply (fact_sub E M a b (uD E a) (uD E b)); try apply u_mod_self; lia. }
       destruct (Z.eqb v 1 && Z.eqb v' 1)%bool eqn:Hv1; [|exact T].
       apply andb_prop in Hv1 as [V1 V2]. apply Z.eqb_eq in V1. apply Z.eqb_eq in V2. subst v v'.
       destruct (Z.ltb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))); [|lia].
       apply (fact_sub E M b a (uD E b) (uD E a)); try apply u_mod_self; lia. }
  2: { destruct (find_s1ok (vc_hyps c)) as [[[[buf len] a1] n]|] eqn:Hs; [|exact T].
       destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v|] eqn:Hr; [|exact T].
       destruct (lin_ge0_h2 kx h [(n, 1)] [(k, 0)] && byte_is34 (vc_kn c) kx buf (recval 4 v))%bool eqn:Hc; [|exact T].
       apply andb_prop in Hc as [Hl Hb]. unfold byte_is34 in Hb.
       destruct (find_rec (vc_kn c) (vc_kn c) [(buf, 0); (recval 4 v, 0)] 1) as [bv|] eqn:Hbr; [|discriminate].
       apply andb_prop in Hb as [B1 B2].
       pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B1) as C1. pose proof (lin_ge0_sound SEGS E M kx _ _ Hkx B2) as C2.
       cbn [xt_den edenot] in C1, C2. rewrite u_lit64a, Z.mod_small in C1, C2 by lia.
       pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
       apply (lin_ge0_h2_sound E M kx) in Hl; [|exact Hkx]. cbn [xt_den] in Hl.
       assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl0 & Hbl & Ha1 & Hn1 & bs & Hin & _).
       pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E n)) as RN. unfold APS.uE in *.
       pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd.
       assert (Had : xt_den E (addr_idx a1 k) = uD E a1 + 4 * uD E k) by (unfold addr_idx; cbn [xt_den]; rewrite xt_den_xN; lia).
       rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * uD E k) 4) with (u32_at M (uD E a1 + 4 * uD E k)) in Hrd.
       replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hrd by reflexivity. rewrite <- recval4 in Hrd.
       assert (Hk1 : 0 <= uD E k <= uD E n + 1) by lia.
       pose proof (idxm_of_rec M _ _ _ _ S1 (uD E k) _ Hk1 Hrd) as HI.
       pose proof (idxm_le_len M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia)) as HIL.
       assert (HB : bv_unsigned (edenot E (recval 1 bv)) = 34) by lia.
       pose proof (u64_range (edenot E buf)) as RB. pose proof (u64_range (edenot E (recval 4 v))) as RX.
       pose proof (input_byte E M (uD E buf) (uD E len) bs (vc_kn c) [(buf, 0); (recval 4 v, 0)] bv ltac:(lia) Hbl Hl0 Hin Hk Hbr) as BY.
       cbn [xt_den] in BY.
       replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E (recval 4 v)) + 0 + 0) - bv_unsigned (edenot E buf))
         with (uD E (recval 4 v)) in BY by lia.
       specialize (BY ltac:(rewrite <- HI; lia)). rewrite HB in BY.
       pose proof (lt_n_of_byte M _ _ _ _ bs S1 Hin (uD E k) Hk1 ltac:(rewrite HI, BY; lia)) as Hkn.
       destruct (idxm_string M _ _ _ _ bs S1 Hin (uD E k) ltac:(lia) ltac:(rewrite HI, BY; reflexivity)) as (j & fq & A & B & _).
       rewrite HI in A. pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
       apply (fact_sub E M len (recval 4 v) (uD E len) (uD E (recval 4 v))); try apply u_mod_self; lia. }
  destruct (find_s1ok (vc_hyps c)) as [[[[buf len] a1] n]|] eqn:Hs; [|exact T].
  destruct (find_rec (vc_kn c) (vc_kn c) (addr_idx a1 k) 4) as [v|] eqn:Hr; [|exact T].
  destruct (lin_ge0_h2 kx h [(n, 0)] [(k, 1)]) eqn:Hl; [|exact T].
  pose proof (find_s1ok_sound E M _ _ _ _ _ Hh Hs) as S1.
  apply (lin_ge0_h2_sound E M kx) in Hl; [|exact Hkx]. cbn [xt_den] in Hl.
  pose proof (rdZ_of_rec E M _ _ _ _ _ Hk Hk Hr) as Hrd.
  assert (S1' := S1). unfold p_s1ok in S1'. destruct S1' as (Hl0 & Hbl & Ha1 & Hn1 & bs & Hin & Hsucc & Hlen & Hb0 & Hidx & _).
  pose proof (u64_range (edenot E k)) as RK. pose proof (u64_range (edenot E a1)) as RA. pose proof (u64_range (edenot E n)) as RN.
  unfold APS.uE in *.
  assert (Had : xt_den E (addr_idx a1 k) = uD E a1 + 4 * uD E k).
  { unfold addr_idx. cbn [xt_den]. rewrite xt_den_xN. lia. }
  rewrite Had in Hrd. change (rdZ M (uD E a1 + 4 * uD E k) 4) with (u32_at M (uD E a1 + 4 * uD E k)) in Hrd.
  pose proof (recval_sound E 4 v ltac:(lia)) as Hx. cbn [Z.of_nat Z.mul Pos.mul] in Hx.
  assert (Hkn : (Z.to_nat (uD E k) < length (fst (S1M.result (nthb bs) (uD E len))))%nat) by lia.
  pose proof (Hidx (Z.to_nat (uD E k)) Hkn) as Hi. rewrite Z2Nat.id in Hi by lia. rewrite Hi in Hrd. injection Hrd as Hv.
  pose proof (S1M.indexes_lt_len (nthb bs) (uD E len) _ (nth_In _ 0 Hkn)) as Hlt. rewrite Hv in Hlt.
  pose proof (hiZ_sound E M (vc_kn c) len Hk) as HL.
  apply (fact_sub E M len (recval 4 v) (uD E len) (uD E (recval 4 v))); try apply u_mod_self; try lia.
  all: rewrite Hx; lia.
Qed.
Lemma add_extras_sound : forall E M c xs kx, know_ok SEGS E M (vc_kn c) -> Forall (APS.gholds GP2 E M) (vc_hyps c) ->
  know_ok SEGS E M kx -> know_ok SEGS E M (add_extras c kx xs).
Proof.
  intros E M c xs. induction xs as [|x rest IH]; intros kx Hk Hh Hkx; cbn [add_extras]; [exact Hkx|].
  apply IH; [exact Hk | exact Hh |]. apply Forall_app. split; [exact Hkx|]. constructor; [|constructor].
  apply extra_fact_sound; assumption.
Qed.

Theorem vc_check_sound : forall r c, vc_check r c = true -> APS.vc_holds SEGS GP2 c.
Proof.
  intros r c H. unfold APS.vc_holds. intros E M Hk Hh.
  pose proof (knx_sound E M c Hk Hh) as HX.
  destruct r as [|i|xs hl hu|hk ht hs|i m hT hS|hk|i d|src recs hd ht|i segs|isrc irecs ihd]; cbn [vc_check] in H.
  - discriminate.
  - destruct (vc_concl c) as [g|K]; [|discriminate].
    destruct (nth_error (vc_hyps c) i) as [g'|] eqn:Hi; [|discriminate].
    apply gatom_eqb_eq in H. subst g'. exact (proj1 (Forall_forall _ _) Hh g (nth_error_In _ _ Hi)).
  - destruct (vc_concl c) as [g|K]; [discriminate|]. destruct K as [| | | | |e lo hi| | | |]; try discriminate.
    eapply krange_h2_sound; [| exact H]. apply add_extras_sound; assumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_acc_init_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_acc_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_str_start_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_str_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_oc_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_strhex_sound E M c (knx c)); eassumption.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. eapply (check_iab_sound E M c (knx c)); eassumption.
Qed.

Theorem vcs_check_sound : forall rs cs, vcs_check rs cs = true -> Forall (APS.vc_holds SEGS GP2) cs.
Proof.
  intros rs. induction rs as [|r rs IH]; intros [|c cs] H; cbn [vcs_check] in H; try discriminate; [constructor|].
  apply andb_prop in H as [Hc Hr]. constructor; [exact (vc_check_sound r c Hc) | exact (IH cs Hr)].
Qed.
End CheckSound.

End WithSegs.

End S2G.
