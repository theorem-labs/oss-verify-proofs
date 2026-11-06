(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1 SjInvPath SjS2Inv SjS2Tab.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2Lin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Definition ONES : Z := 2 ^ 64 - 1.

Section C.
  Variable segs : list Segment.
  Variable TD : Z.          (* [comment removed for export] *)
  Variable MF : Z.          (* [comment removed for export] *)

  Fixpoint find_rb (a : saddr) (n : nat) (sx : bool) (l : list sidecond) : option nat :=
    match l with
    | [] => None
    | SCReadBase a' n' sx' (EVar v) :: r =>
        if (saddr_eqb a a' && Nat.eqb n n' && Bool.eqb sx sx')%bool then Some v else find_rb a n sx r
    | _ :: r => find_rb a n sx r
    end.

  Definition has_sc (s : sidecond) (l : list sidecond) : bool := existsb (SG.sc_eqb s) l.

  Definition bx (v : nat) : expr := EExt false 0 1 (EVar v).

  (* [comment removed for export] *)
  Fixpoint find_rbl (t : expr) (n : nat) (sx : bool) (l : list sidecond) : option nat :=
    match l with
    | [] => None
    | SCReadBase a n' sx' (EVar v) :: r =>
        if (Nat.eqb n n' && Bool.eqb sx sx' && leq (eaddl (a_base a) (a_off a)) t)%bool then Some v else find_rbl t n sx r
    | _ :: r => find_rbl t n sx r
    end.
  (* [comment removed for export] *)
  Definition bvar (B P : expr) (j : Z) (l : list sidecond) : option nat := find_rbl (eaddl (EAlu ALU_ADD B P) j) 1 false l.
  (* [comment removed for export] *)
  Definition tvar (b : nat) (blk : Z) (l : list sidecond) : option nat :=
    find_rb (SA (EMd M_MUL (ELit 4) (bx b)) (TD + 840 * blk)) 4 true l.

  (* [comment removed for export] *)
  Fixpoint or_leaves (e : expr) : option (list nat) :=
    match e with
    | EVar v => Some [v]
    | EAlu ALU_OR a b => match or_leaves a, or_leaves b with Some x, Some y => Some (x ++ y) | _, _ => None end
    | _ => None
    end.
  Definition same_set (x y : list nat) : bool :=
    (forallb (fun v => existsb (Nat.eqb v) y) x && forallb (fun v => existsb (Nat.eqb v) x) y)%bool.
  (* [comment removed for export] *)
  Fixpoint subst_or (ts : list nat) (e : expr) : expr :=
    match e with
    | EAlu ALU_OR a b =>
        match or_leaves e with
        | Some lv => if same_set lv ts then ELit ONES else EAlu ALU_OR (subst_or ts a) (subst_or ts b)
        | None => EAlu ALU_OR (subst_or ts a) (subst_or ts b)
        end
    | EAlu op a b => EAlu op (subst_or ts a) (subst_or ts b)
    | EAluw op a b => EAluw op (subst_or ts a) (subst_or ts b)
    | EMd op a b => EMd op (subst_or ts a) (subst_or ts b)
    | EMdw op a b => EMdw op (subst_or ts a) (subst_or ts b)
    | EExt sx lo n a => EExt sx lo n (subst_or ts a)
    | e => e
    end.

  Fixpoint closed (e : expr) : bool :=
    match e with
    | ELit _ => true
    | EVar _ | EBlob _ _ _ _ => false
    | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (closed a && closed b)%bool
    | EExt _ _ _ a => closed a
    end.

  Definition E0 : env := Env (fun _ => Z_to_bv 64 0) (fun _ => []).

  (* [comment removed for export] *)
  Definition refutes_ones (ts : list nat) (s : sidecond) : bool :=
    match s with
    | SCBr t c a b =>
        let a' := subst_or ts a in let b' := subst_or ts b in
        (closed a' && closed b' && negb (Bool.eqb (branch_taken c (edenot E0 a') (edenot E0 b')) t))%bool
    | _ => false
    end.

  (* [comment removed for export] *)
  Definition hex4_ev (B P : expr) (j : Z) (l : list sidecond) : bool :=
    match bvar B P j l, bvar B P (j + 1) l, bvar B P (j + 2) l, bvar B P (j + 3) l with
    | Some b0, Some b1, Some b2, Some b3 =>
        match tvar b0 3 l, tvar b1 2 l, tvar b2 1 l, tvar b3 0 l with
        | Some t0, Some t1, Some t2, Some t3 => existsb (refutes_ones [t0; t1; t2; t3]) l
        | _, _, _, _ => false
        end
    | _, _, _, _ => false
    end.

  Definition is_byte_eq (v : nat) (c : Z) (l : list sidecond) : bool := has_sc (SCBr true BC_EQ (bx v) (ELit c)) l.
  Definition is_byte_ne (v : nat) (c : Z) (l : list sidecond) : bool :=
    (has_sc (SCBr false BC_EQ (bx v) (ELit c)) l || has_sc (SCBr true BC_NE (bx v) (ELit c)) l)%bool.
  Definition is_byte_eq' (v : nat) (c : Z) (l : list sidecond) : bool :=
    (is_byte_eq v c l || has_sc (SCBr false BC_NE (bx v) (ELit c)) l)%bool.

  (* [comment removed for export] *)
  Definition arm_ok (B P : expr) (k : Z) (l : list sidecond) : bool :=
    match bvar B P 0 l with
    | None => false
    | Some v0 =>
      if Z.eqb k 1 then (is_byte_ne v0 34 l && is_byte_ne v0 92 l)%bool
      else if Z.eqb k 2 then is_byte_eq' v0 92 l
      else if Z.eqb k 6 then
        (is_byte_eq' v0 92 l && match bvar B P 1 l with Some v1 => is_byte_eq' v1 117 l | None => false end && hex4_ev B P 2 l)%bool
      else if Z.eqb k 12 then
        (is_byte_eq' v0 92 l && match bvar B P 1 l with Some v1 => is_byte_eq' v1 117 l | None => false end && hex4_ev B P 2 l
         && match bvar B P 6 l, bvar B P 7 l with
            | Some v6, Some v7 =>
                (has_sc (SCBr true BC_EQ (EAlu ALU_ADD (EMd M_MUL (ELit 256) (bx v6)) (bx v7)) (ELit 23669)) l ||
                 has_sc (SCBr false BC_NE (EAlu ALU_ADD (EMd M_MUL (ELit 256) (bx v6)) (bx v7)) (ELit 23669)) l ||
                 has_sc (SCBr true BC_EQ (EAlu ALU_OR (EMd M_MUL (ELit 256) (bx v6)) (bx v7)) (ELit 23669)) l ||
                 has_sc (SCBr false BC_NE (EAlu ALU_OR (EMd M_MUL (ELit 256) (bx v6)) (bx v7)) (ELit 23669)) l)%bool
            | _, _ => false
            end
         && hex4_ev B P 8 l)%bool
      else false
    end.

  Definition is_pure (K : kentry) : bool := match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true | _ => false end.
  Definition has_kimg (kn : list kentry) (lo hi : Z) : bool :=
    existsb (fun K => match K with KImg a b => (Z.leb a lo && Z.leb hi b)%bool | _ => false end) kn.

  (* [comment removed for export] *)
  Definition str_vc_parts (c : SG.vc) : option (expr * expr * expr * expr * Z) :=
    match SG.vc_src c, SG.vc_tgt c with
    | [ST.GA 0 [B; L; P; Q]], [ST.GA 0 [B'; L'; EAlu ALU_ADD P' (ELit k); Q']] =>
        if (expr_eqb B B' && expr_eqb L L' && expr_eqb P P' && expr_eqb Q Q')%bool then Some (B, L, P, Q, k) else None
    | _, _ => None
    end.

  Definition str_vc_ok (c : SG.vc) : bool :=
    match str_vc_parts c with
    | Some (B, L, P, Q, k) =>
        (Z.leb 1 k && Z.leb k 12 && Z.leb 0 MF &&
         has_kimg (SG.vc_kn c) TD (TD + 3544) && ST.kimplied segs (SG.vc_kn c) (KRange L 0 MF) &&
         arm_ok B P k (SG.vc_path c) &&
         SG.log_apart (SG.vc_kn c) (SG.vc_log c) (gfp 0 [B; L; EAlu ALU_ADD P (ELit k); Q]) &&
         forallb is_pure (SG.vc_facts c) &&
         forallb (ST.kimplied segs (KRange (EAlu ALU_SUB Q (EAlu ALU_ADD P (ELit k))) 0 MF :: SG.vc_kn c)) (SG.vc_facts c))%bool
    | None => false
    end.
End C.

Lemma str_vc_parts_ok : forall c B L P Q k, str_vc_parts c = Some (B, L, P, Q, k) ->
  SG.vc_src c = [ST.GA 0 [B; L; P; Q]] /\ SG.vc_tgt c = [ST.GA 0 [B; L; EAlu ALU_ADD P (ELit k); Q]].
Proof.
  intros [kn path lg src tgt facts] B L P Q k H. unfold str_vc_parts in H. cbn [SG.vc_src SG.vc_tgt] in H |- *.
  repeat (match type of H with
          | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
          end; try discriminate H).
  injection H as <- <- <- <- <-.
  repeat match goal with X : (_ && _)%bool = true |- _ => apply andb_prop in X; destruct X end.
  repeat match goal with X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X; subst end.
  split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma u_rng : forall (w : word), 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma find_rb_in : forall a n sx l v, find_rb a n sx l = Some v -> In (SCReadBase a n sx (EVar v)) l.
Proof.
  intros a n sx l v. induction l as [|s r IH]; cbn [find_rb]; [discriminate|].
  destruct s; try (intros H; right; exact (IH H)).
  destruct e; try (intros H; right; exact (IH H)).
  destruct (saddr_eqb a a0 && Nat.eqb n n0 && Bool.eqb sx sx0)%bool eqn:E.
  - intros H. injection H as <-. left.
    apply andb_prop in E as [E1 E3]. apply andb_prop in E1 as [E1 E2].
    apply saddr_eqb_eq in E1. apply Nat.eqb_eq in E2. apply Bool.eqb_prop in E3. subst. reflexivity.
  - intros H. right. exact (IH H).
Qed.

Lemma find_rbl_in : forall t n sx l v, find_rbl t n sx l = Some v ->
  exists a, In (SCReadBase a n sx (EVar v)) l /\ leq (eaddl (a_base a) (a_off a)) t = true.
Proof.
  intros t n sx l v. induction l as [|s r IH]; cbn [find_rbl]; [discriminate|].
  destruct s; try (intros H; destruct (IH H) as (a' & Hin & Ha); exists a'; split; [right; exact Hin | exact Ha]).
  destruct e; try (intros H; destruct (IH H) as (a' & Hin & Ha); exists a'; split; [right; exact Hin | exact Ha]).
  match goal with |- (if ?cc then _ else _) = _ -> _ => destruct cc eqn:E end.
  - intros H. injection H as <-. apply andb_prop in E as [E1 E3]. apply andb_prop in E1 as [E1 E2].
    apply Nat.eqb_eq in E1. apply Bool.eqb_prop in E2. subst. eexists. split; [left; reflexivity | exact E3].
  - intros H. destruct (IH H) as (a' & Hin & Ha). exists a'. split; [right; exact Hin | exact Ha].
Qed.

Lemma has_sc_in : forall s l, has_sc s l = true -> In s l.
Proof.
  intros s l H. unfold has_sc in H. apply existsb_exists in H as (s' & Hin & E). apply SG.sc_eqb_eq in E. subst. exact Hin.
Qed.

Section Den.
  Variable segs : list Segment.
  Variable m : word -> option byte.
  Variable E : env.
  Variable l : list sidecond.
  Hypothesis HP : scs_denot segs m E l.

  Lemma sc_of_in : forall s, In s l -> sc_denot segs m E s.
  Proof. intros s Hs. exact (proj1 (Forall_forall _ _) HP s Hs). Qed.

  (* [comment removed for export] *)
  Lemma rb1_val : forall a v, In (SCReadBase a 1 false (EVar v)) l ->
    bv_unsigned (ev E v) = mbyte segs m (bv_unsigned (adenot E a)) /\ bv_unsigned (ev E v) < 256.
  Proof.
    intros a v Hin. pose proof (sc_of_in _ Hin) as (bs & Hr & Hv). cbn [sc_denot edenot] in Hv.
    unfold mbyte. rewrite Z_to_bv_bv_unsigned, Hr.
    destruct bs as [|b [|b' bs']].
    - cbn in Hr. destruct (match m (adenot E a) with Some b => Some b | None => seg_rom segs (adenot E a) end); [|discriminate].
      destruct (rdn segs m (adenot E a + 1) 0); discriminate.
    - cbn [extz bytes_le_to_Z] in Hv. rewrite <- Hv. rewrite Z.shiftl_0_l, Z.lor_0_r.
      pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      rewrite u_lit by lia. split; [reflexivity| lia].
    - exfalso. pose proof (rdn_length segs m 1 (adenot E a) _ Hr) as HL. cbn in HL. discriminate.
  Qed.
End Den.

(* [comment removed for export] *)
Lemma u_add : forall (a b : word), bv_unsigned a + bv_unsigned b < 2 ^ 64 ->
  bv_unsigned (alu64 ALU_ADD a b) = bv_unsigned a + bv_unsigned b.
Proof.
  intros a b H. cbn [alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  pose proof (u_rng a). pose proof (u_rng b). apply Z.mod_small. lia.
Qed.

Lemma u_sub : forall (a b : word), bv_unsigned b <= bv_unsigned a ->
  bv_unsigned (alu64 ALU_SUB a b) = bv_unsigned a - bv_unsigned b.
Proof.
  intros a b H. cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  pose proof (u_rng a). pose proof (u_rng b). apply Z.mod_small. lia.
Qed.

Lemma u_adenot_add : forall E B P j, 0 <= j -> bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j < 2 ^ 64 ->
  bv_unsigned (adenot E (SA (EAlu ALU_ADD B P) j)) = bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j.
Proof.
  intros E B P j Hj H. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
  pose proof (u_rng (edenot E B)). pose proof (u_rng (edenot E P)).
  rewrite u_add by lia. apply u_lit. lia.
Qed.

Lemma u_bx : forall E v, bv_unsigned (ev E v) < 256 -> bv_unsigned (edenot E (bx v)) = bv_unsigned (ev E v).
Proof.
  intros E v H. unfold bx. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. pose proof (u_rng (ev E v)). rewrite (Z.mod_small _ 256) by lia. apply u_lit. lia.
Qed.

Lemma br_eq_lit : forall (a : word) c t, 0 <= c < 2 ^ 64 -> branch_taken BC_EQ a (Z_to_bv 64 c) = t ->
  (t = true -> bv_unsigned a = c) /\ (t = false -> bv_unsigned a <> c).
Proof.
  intros a c t Hc H. cbn [branch_taken] in H. unfold bv_eqb in H. rewrite u_lit in H by lia.
  split; intros ->; [apply Z.eqb_eq; exact H| apply Z.eqb_neq; exact H].
Qed.

Lemma br_ne_lit : forall (a : word) c t, 0 <= c < 2 ^ 64 -> branch_taken BC_NE a (Z_to_bv 64 c) = t ->
  (t = true -> bv_unsigned a <> c) /\ (t = false -> bv_unsigned a = c).
Proof.
  intros a c t Hc H. cbn [branch_taken] in H. unfold bv_eqb in H. rewrite u_lit in H by lia.
  split; intros ->; [apply negb_true_iff in H; apply Z.eqb_neq; exact H| apply negb_false_iff in H; apply Z.eqb_eq; exact H].
Qed.

(* [comment removed for export] *)
Lemma byte_is : forall segs m E l v c, scs_denot segs m E l -> bv_unsigned (ev E v) < 256 -> 0 <= c < 256 ->
  (has_sc (SCBr true BC_EQ (bx v) (ELit c)) l = true \/ has_sc (SCBr false BC_NE (bx v) (ELit c)) l = true) ->
  bv_unsigned (ev E v) = c.
Proof.
  intros segs m E l v c HP Hv Hc [H|H]; apply has_sc_in in H; pose proof (sc_of_in segs m E l HP _ H) as D; cbn [sc_denot] in D;
    rewrite edenot_lit in D; rewrite <- (u_bx E v Hv).
  - exact (proj1 (br_eq_lit _ c true ltac:(lia) D) eq_refl).
  - exact (proj2 (br_ne_lit _ c false ltac:(lia) D) eq_refl).
Qed.

Lemma byte_isnt : forall segs m E l v c, scs_denot segs m E l -> bv_unsigned (ev E v) < 256 -> 0 <= c < 256 ->
  (has_sc (SCBr false BC_EQ (bx v) (ELit c)) l = true \/ has_sc (SCBr true BC_NE (bx v) (ELit c)) l = true) ->
  bv_unsigned (ev E v) <> c.
Proof.
  intros segs m E l v c HP Hv Hc [H|H]; apply has_sc_in in H; pose proof (sc_of_in segs m E l HP _ H) as D; cbn [sc_denot] in D;
    rewrite edenot_lit in D; rewrite <- (u_bx E v Hv).
  - exact (proj2 (br_eq_lit _ c false ltac:(lia) D) eq_refl).
  - exact (proj1 (br_ne_lit _ c true ltac:(lia) D) eq_refl).
Qed.

(* [comment removed for export] *)
Definition ones_w : word := Z_to_bv 64 ONES.

Lemma u_ones : bv_unsigned ones_w = ONES.
Proof. unfold ones_w, ONES. apply u_lit. lia. Qed.

Lemma lor_ones_l : forall y, 0 <= y < 2 ^ 64 -> Z.lor ONES y = ONES.
Proof.
  intros y Hy. unfold ONES. change (2 ^ 64 - 1) with (Z.ones 64). apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec. destruct (Z.lt_ge_cases n 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec y 0) as [->|N]; [cbn; lia|]. apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma bv_or_ones : forall (x y : word), x = ones_w \/ y = ones_w -> bv_or x y = ones_w.
Proof.
  intros x y H. apply bv_eq. rewrite bv_or_unsigned, u_ones. pose proof (u_rng x). pose proof (u_rng y).
  destruct H as [->| ->]; rewrite u_ones; [apply lor_ones_l; lia| rewrite Z.lor_comm; apply lor_ones_l; lia].
Qed.

Lemma or_leaves_ones : forall E X lv, or_leaves X = Some lv -> (exists t, In t lv /\ ev E t = ones_w) -> edenot E X = ones_w.
Proof.
  intros E X. induction X as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    intros lv H (t & Ht & Hv); cbn [or_leaves] in H; try discriminate.
  - injection H as <-. destruct Ht as [<-|[]]. exact Hv.
  - destruct op; try discriminate.
    destruct (or_leaves a) as [la|] eqn:Ea; [|discriminate]. destruct (or_leaves b) as [lb|] eqn:Eb; [|discriminate].
    injection H as <-. cbn [edenot alu64 alu]. apply bv_or_ones.
    apply in_app_or in Ht as [Ht|Ht]; [left; apply (IHa la eq_refl); eauto | right; apply (IHb lb eq_refl); eauto].
Qed.

Lemma same_set_sub : forall x y v, same_set x y = true -> In v y -> In v x.
Proof.
  intros x y v H Hv. unfold same_set in H. apply andb_prop in H as [_ H2].
  pose proof (proj1 (forallb_forall _ _) H2 v Hv) as X. apply existsb_exists in X as (w & Hw & E). apply Nat.eqb_eq in E. subst. exact Hw.
Qed.

Lemma subst_or_eq : forall E ts e, (exists t, In t ts /\ ev E t = ones_w) -> edenot E (subst_or ts e) = edenot E e.
Proof.
  intros E ts e Hex. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [subst_or]; try reflexivity.
  - destruct op; cbn [edenot]; try (rewrite IHa, IHb; reflexivity).
    destruct (or_leaves (EAlu ALU_OR a b)) as [lv|] eqn:E1; [|cbn [edenot]; rewrite IHa, IHb; reflexivity].
    destruct (same_set lv ts) eqn:E2; [|cbn [edenot]; rewrite IHa, IHb; reflexivity].
    rewrite edenot_lit. symmetry. apply (or_leaves_ones E _ lv E1).
    destruct Hex as (t & Ht & Hv). exists t. split; [exact (same_set_sub lv ts t E2 Ht)| exact Hv].
  - cbn [edenot]. rewrite IHa, IHb. reflexivity.
  - cbn [edenot]. rewrite IHa, IHb. reflexivity.
  - cbn [edenot]. rewrite IHa, IHb. reflexivity.
  - cbn [edenot]. rewrite IHa. reflexivity.
Qed.

Lemma closed_edenot : forall E e, closed e = true -> edenot E e = edenot E0 e.
Proof.
  intros E e. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [closed]; intros H; try discriminate; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; cbn [edenot]; rewrite (IHa H1), (IHb H2); reflexivity).
  cbn [edenot]. rewrite (IHa H). reflexivity.
Qed.

Lemma refutes_ones_sound : forall segs m E ts s, refutes_ones ts s = true -> sc_denot segs m E s ->
  ~ (exists t, In t ts /\ ev E t = ones_w).
Proof.
  intros segs m E ts s H D Hex. destruct s as [t c a b| | | | | |]; cbn [refutes_ones] in H; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [sc_denot] in D.
  rewrite <- (subst_or_eq E ts a Hex), <- (subst_or_eq E ts b Hex), (closed_edenot E _ H1), (closed_edenot E _ H2) in D.
  rewrite D in H3. rewrite Bool.eqb_reflx in H3. discriminate.
Qed.

(* [comment removed for export] *)
Section Tab.
  Variable segs : list Segment.
  Variable TD : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).

  Lemma u_mul4_bx : forall E b, bv_unsigned (ev E b) < 256 ->
    bv_unsigned (edenot E (EMd M_MUL (ELit 4) (bx b))) = 4 * bv_unsigned (ev E b).
  Proof.
    intros E b Hb. change (edenot E (EMd M_MUL (ELit 4) (bx b))) with (mul_div M_MUL (Z_to_bv 64 4) (edenot E (bx b))).
    cbn [mul_div]. rewrite bv_mul_unsigned, u_lit by lia. rewrite (u_bx E b Hb). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    pose proof (u_rng (ev E b)). apply Z.mod_small. lia.
  Qed.

  Lemma tvar_val : forall m E l b t blk, scs_denot segs m E l -> (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) ->
    bv_unsigned (ev E b) < 256 -> 0 <= blk <= 3 ->
    In (SCReadBase (SA (EMd M_MUL (ELit 4) (bx b)) (TD + 840 * blk)) 4 true (EVar t)) l ->
    ev E t = Z_to_bv 64 (bv_swrap 32 (d2v_blk blk (bv_unsigned (ev E b)))).
  Proof.
    intros m E l b t blk HP HU Hb Hblk Hin. pose proof (sc_of_in segs m E l HP _ Hin) as (bs & Hr & Hv).
    cbn [edenot] in Hv. rewrite <- Hv.
    unfold adenot in Hr. cbn [a_base a_off] in Hr. unfold v_addi in Hr. rewrite u_mul4_bx in Hr by exact Hb.
    replace (4 * bv_unsigned (ev E b) + (TD + 840 * blk)) with (TD + 4 * (210 * blk + bv_unsigned (ev E b))) in Hr by lia.
    pose proof (u_rng (ev E b)).
    rewrite (D2V_IMG m (210 * blk + bv_unsigned (ev E b)) HU) in Hr by lia. injection Hr as <-.
    rewrite d2v_read by lia. unfold word_to_le_bytes. pose proof (d2v_blk_range blk (bv_unsigned (ev E b)) Hblk) as DR.
    rewrite u_lit by lia. rewrite bytes_le_to_Z_of_le_bytes by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite Z.mod_small by lia. cbn [extz]. change (8 * N.of_nat 4)%N with 32%N. reflexivity.
  Qed.

  Lemma tvar_ones : forall m E l b t blk, scs_denot segs m E l -> (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) ->
    bv_unsigned (ev E b) < 256 -> 0 <= blk <= 3 ->
    In (SCReadBase (SA (EMd M_MUL (ELit 4) (bx b)) (TD + 840 * blk)) 4 true (EVar t)) l ->
    hexval (bv_unsigned (ev E b)) = None -> ev E t = ones_w.
  Proof.
    intros m E l b t blk HP HU Hb Hblk Hin Hh. rewrite (tvar_val m E l b t blk HP HU Hb Hblk Hin).
    unfold d2v_blk. rewrite Hh. unfold ones_w, ONES. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bvar_val : forall m E l B P j v, scs_denot segs m E l -> 0 <= j ->
    bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j < 2 ^ 64 ->
    bvar B P j l = Some v ->
    bv_unsigned (ev E v) = mbyte segs m (bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j) /\ bv_unsigned (ev E v) < 256.
  Proof.
    clear TD_rng D2V_IMG. intros m E l B P j v HP Hj Hr H. apply find_rbl_in in H as (a & Hin & HA).
    destruct (rb1_val segs m E l HP _ _ Hin) as [H1 H2].
    rewrite (adenot_lin E a B P j HA Hj Hr) in H1. split; assumption.
  Qed.

  Lemma hex4_ev_sound : forall m E l B P j, scs_denot segs m E l -> (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) ->
    0 <= j -> bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j + 3 < 2 ^ 64 ->
    hex4_ev TD B P j l = true ->
    forall i, 0 <= i < 4 -> hexval (mbyte segs m (bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j + i)) <> None.
  Proof.
    intros m E l B P j HP HU Hj Hr H i Hi Hn. unfold hex4_ev in H.
    destruct (bvar B P j l) as [b0|] eqn:B0; [|discriminate]. destruct (bvar B P (j + 1) l) as [b1|] eqn:B1; [|discriminate].
    destruct (bvar B P (j + 2) l) as [b2|] eqn:B2; [|discriminate]. destruct (bvar B P (j + 3) l) as [b3|] eqn:B3; [|discriminate].
    destruct (tvar TD b0 3 l) as [t0|] eqn:T0; [|discriminate]. destruct (tvar TD b1 2 l) as [t1|] eqn:T1; [|discriminate].
    destruct (tvar TD b2 1 l) as [t2|] eqn:T2; [|discriminate]. destruct (tvar TD b3 0 l) as [t3|] eqn:T3; [|discriminate].
    apply existsb_exists in H as (s & Hs & Hrf).
    apply (refutes_ones_sound segs m E _ s Hrf (sc_of_in segs m E l HP s Hs)).
    destruct (bvar_val m E l B P j b0 HP ltac:(lia) ltac:(lia) B0) as [V0 R0].
    destruct (bvar_val m E l B P (j + 1) b1 HP ltac:(lia) ltac:(lia) B1) as [V1 R1].
    destruct (bvar_val m E l B P (j + 2) b2 HP ltac:(lia) ltac:(lia) B2) as [V2 R2].
    destruct (bvar_val m E l B P (j + 3) b3 HP ltac:(lia) ltac:(lia) B3) as [V3 R3].
    unfold tvar in T0, T1, T2, T3. apply find_rb_in in T0, T1, T2, T3.
    assert (I4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct I4 as [-> | [-> | [-> | ->]]].
    - exists t0. split; [cbn; tauto|]. apply (tvar_ones m E l b0 t0 3 HP HU R0 ltac:(lia)); [exact T0|]. rewrite V0. rewrite Z.add_0_r in Hn. exact Hn.
    - exists t1. split; [cbn; tauto|]. apply (tvar_ones m E l b1 t1 2 HP HU R1 ltac:(lia)); [exact T1|]. rewrite V1. replace (_ + _ + (j + 1)) with (bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j + 1) by lia. exact Hn.
    - exists t2. split; [cbn; tauto|]. apply (tvar_ones m E l b2 t2 1 HP HU R2 ltac:(lia)); [exact T2|]. rewrite V2. replace (_ + _ + (j + 2)) with (bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j + 2) by lia. exact Hn.
    - exists t3. split; [cbn; tauto|]. apply (tvar_ones m E l b3 t3 0 HP HU R3 ltac:(lia)); [exact T3|]. rewrite V3. replace (_ + _ + (j + 3)) with (bv_unsigned (edenot E B) + bv_unsigned (edenot E P) + j + 3) by lia. exact Hn.
  Qed.
End Tab.

(* [comment removed for export] *)
Section Arms.
  Variable segs : list Segment.
  Variable TD : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).

  Variable m : word -> option byte.
  Variable E : env.
  Variable l : list sidecond.
  Hypothesis HP : scs_denot segs m E l.
  Hypothesis HU : forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None.
  Variables (B P : expr) (uL uQ : Z).
  Notation uB := (bv_unsigned (edenot E B)).
  Notation uP := (bv_unsigned (edenot E P)).
  Notation D := (mdata segs m uB uL).
  Hypothesis HBL : uB + uL + 64 < 2 ^ 64.
  Hypothesis HQL : uQ < uL.

  Lemma byte_here : forall x, bpath D uL x uQ -> 0 <= x -> dbyte D x = mbyte segs m (uB + x).
  Proof.
    intros x H Hx. pose proof (bpath_bound _ _ _ _ H). unfold dbyte. rewrite mdata_byte by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bvar_data : forall j v, 0 <= j -> bpath D uL (uP + j) uQ -> bvar B P j l = Some v ->
    bv_unsigned (ev E v) = dbyte D (uP + j) /\ bv_unsigned (ev E v) < 256.
  Proof.
    intros j v Hj H Hv. pose proof (bpath_bound _ _ _ _ H). pose proof (u_rng (edenot E P)).
    destruct (bvar_val segs m E l B P j v HP Hj ltac:(lia) Hv) as [V R]. split; [|exact R].
    rewrite V, (byte_here (uP + j) H) by lia. f_equal. lia.
  Qed.

  Lemma step_hex : forall a, bpath D uL a uQ -> 0 <= a -> hexval (mbyte segs m (uB + a)) <> None -> bpath D uL (a + 1) uQ.
  Proof.
    intros a H Ha Hh. pose proof (byte_here a H Ha) as Hb. unfold dbyte in Hb.
    destruct (hexval (mbyte segs m (uB + a))) as [v|] eqn:E1; [|congruence]. pose proof (hexval_some_hex _ _ E1) as X.
    apply bpath_inv_plain; [exact H| |]; rewrite Hb; lia.
  Qed.

  Lemma step_hex4 : forall j, 0 <= j -> uB + uP + j + 3 < 2 ^ 64 -> hex4_ev TD B P j l = true ->
    bpath D uL (uP + j) uQ -> bpath D uL (uP + j + 4) uQ.
  Proof.
    intros j Hj Hr Hev H. pose proof (u_rng (edenot E P)).
    pose proof (hex4_ev_sound segs TD TD_rng D2V_IMG m E l B P j HP HU Hj Hr Hev) as HX.
    assert (A : forall i, 0 <= i < 4 -> bpath D uL (uP + j + i) uQ -> bpath D uL (uP + j + i + 1) uQ).
    { intros i Hi Hi'. apply step_hex; [exact Hi'| lia|]. replace (uB + (uP + j + i)) with (uB + uP + j + i) by lia. apply HX. exact Hi. }
    replace (uP + j + 4) with (uP + j + 3 + 1) by lia. apply A; [lia|].
    replace (uP + j + 3) with (uP + j + 2 + 1) by lia. apply A; [lia|].
    replace (uP + j + 2) with (uP + j + 1 + 1) by lia. apply A; [lia|].
    replace (uP + j + 1) with (uP + j + 0 + 1) by lia. apply A; [lia|]. rewrite Z.add_0_r. exact H.
  Qed.

  Lemma arm_sound : bpath D uL uP uQ -> forall k, arm_ok TD B P k l = true -> bpath D uL (uP + k) uQ.
  Proof.
    intros H k Ha. pose proof (bpath_bound _ _ _ _ H) as [Hpq _]. pose proof (u_rng (edenot E P)). pose proof (u_rng (edenot E B)).
    unfold arm_ok in Ha. destruct (bvar B P 0 l) as [v0|] eqn:V0; [|discriminate].
    destruct (bvar_data 0 v0 ltac:(lia) ltac:(rewrite Z.add_0_r; exact H) V0) as [D0 R0]. rewrite Z.add_0_r in D0. unfold dbyte in D0.
    destruct (Z.eqb_spec k 1) as [->|N1].
    { apply andb_prop in Ha as [A1 A2].
      apply bpath_inv_plain; [exact H| |]; rewrite <- D0.
      - apply (byte_isnt segs m E l v0 34 HP R0 ltac:(lia)). unfold is_byte_ne in A1. apply orb_prop in A1. exact A1.
      - apply (byte_isnt segs m E l v0 92 HP R0 ltac:(lia)). unfold is_byte_ne in A2. apply orb_prop in A2. exact A2. }
    assert (BS : is_byte_eq' v0 92 l = true -> bpath D uL (uP + 2) uQ).
    { intros A. apply bpath_inv_esc; [exact H|]. rewrite <- D0.
      apply (byte_is segs m E l v0 92 HP R0 ltac:(lia)). unfold is_byte_eq', is_byte_eq in A. apply orb_prop in A. exact A. }
    destruct (Z.eqb_spec k 2) as [->|N2]; [exact (BS Ha)|].
    destruct (Z.eqb_spec k 6) as [->|N6].
    { apply andb_prop in Ha as [A H4]. apply andb_prop in A as [A _]. pose proof (BS A) as H2.
      pose proof (bpath_bound _ _ _ _ H2) as [H2q _].
      replace (uP + 6) with (uP + 2 + 4) by lia. apply (step_hex4 2); [lia|lia|exact H4|exact H2]. }
    destruct (Z.eqb_spec k 12) as [->|N12]; [|discriminate].
    apply andb_prop in Ha as [A H8]. apply andb_prop in A as [A H67]. apply andb_prop in A as [A H4]. apply andb_prop in A as [A _].
    pose proof (BS A) as H2. pose proof (bpath_bound _ _ _ _ H2) as [H2q _].
    pose proof (step_hex4 2 ltac:(lia) ltac:(lia) H4 H2) as H6.
    replace (uP + 2 + 4) with (uP + 6) in H6 by lia. pose proof (bpath_bound _ _ _ _ H6) as [H6q _].
    destruct (bvar B P 6 l) as [v6|] eqn:V6; [|discriminate]. destruct (bvar B P 7 l) as [v7|] eqn:V7; [|discriminate].
    destruct (bvar_data 6 v6 ltac:(lia) H6 V6) as [D6 R6].
    destruct (bvar_val segs m E l B P 7 v7 HP ltac:(lia) ltac:(lia) V7) as [_ R7].
    assert (M6 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 256) (ext_val false 0 1 (ev E v6))) = 256 * bv_unsigned (ev E v6)).
    { cbn [mul_div]. rewrite bv_mul_unsigned, u_lit by lia. change (ext_val false 0 1 (ev E v6)) with (edenot E (bx v6)). rewrite (u_bx E v6 R6).
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). pose proof (u_rng (ev E v6)). apply Z.mod_small. lia. }
    assert (QA : bv_unsigned (edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 256) (bx v6)) (bx v7))) = 23669 \/
                 bv_unsigned (edenot E (EAlu ALU_OR (EMd M_MUL (ELit 256) (bx v6)) (bx v7))) = 23669).
    { repeat (apply orb_prop in H67 as [H67|H67]); apply has_sc_in in H67; pose proof (sc_of_in segs m E l HP _ H67) as Q67;
        cbn [sc_denot] in Q67.
      - left. exact (proj1 (br_eq_lit _ 23669 true ltac:(lia) Q67) eq_refl).
      - left. exact (proj2 (br_ne_lit _ 23669 false ltac:(lia) Q67) eq_refl).
      - right. exact (proj1 (br_eq_lit _ 23669 true ltac:(lia) Q67) eq_refl).
      - right. exact (proj2 (br_ne_lit _ 23669 false ltac:(lia) Q67) eq_refl). }
    assert (Q1 : 256 * bv_unsigned (ev E v6) + bv_unsigned (ev E v7) = 23669).
    { destruct QA as [Q1|Q1].
      - cbn [edenot alu64 alu] in Q1. rewrite bv_add_unsigned in Q1.
        change (edenot E (bx v6)) with (ext_val false 0 1 (ev E v6)) in Q1. rewrite M6 in Q1.
        change (ext_val false 0 1 (ev E v7)) with (edenot E (bx v7)) in Q1. rewrite (u_bx E v7 R7) in Q1.
        unfold bv_wrap, bv_modulus in Q1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Q1.
        rewrite Z.mod_small in Q1 by (pose proof (u_rng (ev E v7)); pose proof (u_rng (ev E v6)); lia). exact Q1.
      - cbn [edenot alu64 alu] in Q1. rewrite bv_or_unsigned in Q1.
        change (edenot E (bx v6)) with (ext_val false 0 1 (ev E v6)) in Q1. rewrite M6 in Q1.
        change (ext_val false 0 1 (ev E v7)) with (edenot E (bx v7)) in Q1. rewrite (u_bx E v7 R7) in Q1.
        pose proof (u_rng (ev E v7)). pose proof (u_rng (ev E v6)).
        rewrite <- Q1. symmetry. rewrite <- Z.lxor_lor.
        + rewrite Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
          destruct (Z_lt_ge_dec k 8) as [Lt|Ge].
          * replace (256 * bv_unsigned (ev E v6)) with (Z.shiftl (bv_unsigned (ev E v6)) 8) by (rewrite Z.shiftl_mul_pow2; lia).
            rewrite Z.shiftl_spec_low by lia. reflexivity.
          * rewrite (Z.bits_above_log2 (bv_unsigned (ev E v7)) k); [apply andb_false_r| lia |].
            destruct (Z.eq_dec (bv_unsigned (ev E v7)) 0) as [->|N]; [cbn; lia|]. apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia.
        + apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
          destruct (Z_lt_ge_dec k 8) as [Lt|Ge].
          * replace (256 * bv_unsigned (ev E v6)) with (Z.shiftl (bv_unsigned (ev E v6)) 8) by (rewrite Z.shiftl_mul_pow2; lia).
            rewrite Z.shiftl_spec_low by lia. reflexivity.
          * rewrite (Z.bits_above_log2 (bv_unsigned (ev E v7)) k); [apply andb_false_r| lia |].
            destruct (Z.eq_dec (bv_unsigned (ev E v7)) 0) as [->|N]; [cbn; lia|]. apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia. }
    assert (B6 : bv_unsigned (ev E v6) = 92) by (pose proof (u_rng (ev E v7)); pose proof (u_rng (ev E v6)); lia).
    assert (H8' : bpath D uL (uP + 8) uQ).
    { replace (uP + 8) with (uP + 6 + 2) by lia. apply bpath_inv_esc; [exact H6|]. unfold dbyte in D6. rewrite <- D6. exact B6. }
    pose proof (bpath_bound _ _ _ _ H8') as [H8q _].
    replace (uP + 12) with (uP + 8 + 4) by lia. apply (step_hex4 8); [lia|lia|exact H8|exact H8'].
  Qed.
End Arms.

(* [comment removed for export] *)
Section Main.
  Variable segs : list Segment.
  Variables TD MF : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).

  Lemma has_kimg_ok : forall E m kn lo hi, know_ok segs E m kn -> has_kimg kn lo hi = true ->
    forall x, lo <= x < hi -> m (Z_to_bv 64 x) = None.
  Proof.
    intros E m kn lo hi HK H x Hx. unfold has_kimg in H. apply existsb_exists in H as (K & Hin & HK1).
    destruct K; try discriminate. apply andb_prop in HK1 as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as D. cbn [kentry_ok] in D. destruct D as (_ & _ & D). apply D. lia.
  Qed.

  Lemma pure_ok : forall E m m' K, is_pure K = true -> kentry_ok segs E m K -> kentry_ok segs E m' K.
  Proof. intros E m m' K H D. destruct K; try discriminate; exact D. Qed.

  Theorem str_vc_ok_sound : forall c, str_vc_ok segs TD MF c = true -> SG.vc_holds segs (GP segs) c.
  Proof.
    intros c H. unfold str_vc_ok in H. destruct (str_vc_parts c) as [[[[[B L] P'] Q] k]|] eqn:EP; [|discriminate].
    destruct (str_vc_parts_ok c B L P' Q k EP) as [HSRC HTGT].
    destruct c as [kn path lg src tgt facts]. cbn [SG.vc_src SG.vc_tgt SG.vc_kn SG.vc_path SG.vc_log SG.vc_facts] in *. subst src tgt.
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H; destruct H as [H ?] end.
    repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X end.
    intros E m HK HPth HL HS.
    unfold SG.gholds in HS. inversion HS as [|g l0 HG _]; subst. cbn [ST.g_id ST.g_args map GP] in HG.
    destruct HG as (HBL & HQL & HPATH).
    (* [comment removed for export] *)
    match goal with X : has_kimg kn TD (TD + 3544) = true |- _ => pose proof (has_kimg_ok E m kn _ _ HK X) as HU end.
    match goal with X : ST.kimplied segs kn (KRange L 0 MF) = true |- _ => pose proof (ST.kimplied_ok segs E m kn _ HK X) as HLM end.
    cbn [kentry_ok] in HLM.
    match goal with X : arm_ok TD B P' k path = true |- _ => rename X into HARM end.
    assert (HNEW : bpath (mdata segs m (bv_unsigned (edenot E B)) (bv_unsigned (edenot E L))) (bv_unsigned (edenot E L))
                         (bv_unsigned (edenot E P') + k) (bv_unsigned (edenot E Q))) by (eapply arm_sound; eauto).
    pose proof (bpath_bound _ _ _ _ HNEW) as [HPk _].
    pose proof (u_rng (edenot E P')). pose proof (u_rng (edenot E B)). pose proof (u_rng (edenot E L)). pose proof (u_rng (edenot E Q)).
    assert (UPk : bv_unsigned (edenot E (EAlu ALU_ADD P' (ELit k))) = bv_unsigned (edenot E P') + k).
    { cbn [edenot]. rewrite u_add; rewrite u_lit by lia; lia. }
    split.
    - (* [comment removed for export] *)
      unfold SG.gholds. constructor; [|constructor]. cbn [ST.g_id ST.g_args].
      apply (gp_frame segs 0%nat [B; L; EAlu ALU_ADD P' (ELit k); Q] E m (mem_denot E m lg)).
      + intros x Hx. eapply SG.mem_denot_apart; [exact HK | exact HL | exact H2 | exact Hx].
      + cbn [map GP]. split; [exact HBL|]. split; [exact HQL|]. rewrite UPk. exact HNEW.
    - (* [comment removed for export] *)
      match goal with X : forallb is_pure facts = true |- _ => rename X into HPURE end.
      match goal with X : forallb (ST.kimplied segs _) facts = true |- _ => rename X into HIMP end.
      assert (HK' : know_ok segs E m (KRange (EAlu ALU_SUB Q (EAlu ALU_ADD P' (ELit k))) 0 MF :: kn)).
      { constructor; [|exact HK]. cbn [kentry_ok].
        change (edenot E (EAlu ALU_SUB Q (EAlu ALU_ADD P' (ELit k)))) with (alu64 ALU_SUB (edenot E Q) (edenot E (EAlu ALU_ADD P' (ELit k)))).
        rewrite u_sub by lia. lia. }
      pose proof (ST.kimplied_all_ok segs E m _ facts HK' HIMP) as HF.
      unfold know_ok in HF |- *. apply Forall_forall. intros K HKin.
      apply (pure_ok E m); [exact (proj1 (forallb_forall _ _) HPURE K HKin)| exact (proj1 (Forall_forall _ _) HF K HKin)].
  Qed.
End Main.
