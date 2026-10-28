(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0DiagChk_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. pose proof (bv_unsigned_in_range _ (getr R (reg k))) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma pcw z (w : word) : bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros <-. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma rdn_ext_Z (M M' : word -> option byte) a k :
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (forall x : word, a <= bv_unsigned x < a + Z.of_nat k -> M' x = M x) ->
  rdn RSEGS M' (Z_to_bv 64 a) k = rdn RSEGS M (Z_to_bv 64 a) k.
Proof.
  intros Ha Hk AG. destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]. { replace k with 0%nat by lia. reflexivity. }
  apply rdn_ext; rewrite L5.unsigned_lit by lia; [lia | exact AG].
Qed.
Lemma u64_ext M M' a v : (forall x : word, a <= bv_unsigned x < a + 8 -> M' x = M x) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros AG Ha Hb C. unfold L5.u64_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma u32_ext M M' a v : (forall x : word, a <= bv_unsigned x < a + 4 -> M' x = M x) -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros AG Ha Hb C. unfold L5.u32_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma u8_ext M M' a v : (forall x : word, a <= bv_unsigned x < a + 1 -> M' x = M x) -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v.
Proof. intros AG Ha Hb C. unfold L5.u8_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma rdn_xfer (M M' : word -> option byte) a k bs : (forall x : word, a <= bv_unsigned x < a + Z.of_nat k -> M' x = M x) -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) k = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) k = Some bs.
Proof. intros AG Ha Hb C. rewrite <- C. apply rdn_ext_Z; assumption. Qed.
Lemma zeros_ext M M' a n : (forall x : word, a <= bv_unsigned x < a + n -> M' x = M x) -> 0 <= a -> a + n <= 2 ^ 64 -> L5KA.zeros_at M a n -> L5KA.zeros_at M' a n.
Proof. intros AG Ha Hb Z0 i Hi. rewrite AG; [apply Z0; exact Hi | rewrite L5.unsigned_lit by lia; lia]. Qed.
Lemma imgc_ext M M' lo hi : (forall x : word, lo <= bv_unsigned x < hi -> M' x = M x) -> 0 <= lo -> hi <= 2 ^ 64 -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros AG Ha Hb Z0 i Hi. rewrite AG; [apply Z0; exact Hi | rewrite L5.unsigned_lit by lia; lia]. Qed.
Lemma defined_grows M M' a n : mem_grows M M' -> L5.defined M a n -> L5.defined M' a n.
Proof. intros G D i Hi. apply G. apply D. exact Hi. Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> L5.writable RSEGS M a n -> L5.writable RSEGS M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma pw_ext (M M' : word -> option byte) (P : Z -> Prop) (b : byte) :
  (forall x : word, P (bv_unsigned x) -> M' x = M x) -> (forall x : word, P (bv_unsigned x) -> M x = Some b) -> forall x : word, P (bv_unsigned x) -> M' x = Some b.
Proof. intros AG H x Hx. rewrite AG by exact Hx. apply H. exact Hx. Qed.

(* [comment removed for export] *)
Lemma store_ok_of_writable M a n (k : nat) : L5.writable RSEGS M a n -> Z.of_nat k = n -> store_ok RSEGS M (Z_to_bv 64 a) k = true.
Proof. intros W E. specialize (W 0 k ltac:(lia) ltac:(lia)). rewrite Z.add_0_r in W. exact W. Qed.
Lemma store_ok_of_writable_sub M a n a' (k : nat) : L5.writable RSEGS M a n -> a <= a' -> a' + Z.of_nat k <= a + n -> store_ok RSEGS M (Z_to_bv 64 a') k = true.
Proof. intros W H1 H2. specialize (W (a' - a) k ltac:(lia) ltac:(lia)). replace (a + (a' - a)) with a' in W by lia. exact W. Qed.

(* [comment removed for export] *)
Lemma regk (k : nat) (r : Prelude.reg) : bv_unsigned r = Z.of_nat k -> reg k = r.
Proof. intros H. rewrite <- H. apply Z_to_bv_bv_unsigned. Qed.
Lemma getr_reg (R : bvmap 5 word) k (r : Prelude.reg) : bv_unsigned r = Z.of_nat k -> getr R (reg k) = getr R r.
Proof. intros H. rewrite (regk k r H). reflexivity. Qed.
Lemma wlit (w : word) : w = Z_to_bv 64 (bv_unsigned w).
Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* [comment removed for export] *)
Lemma keeps_cs_reg (R R' : bvmap 5 word) k : keeps_cs R R' -> In k [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k).
Proof.
  intros K Hk. cbn in Hk.
  repeat (destruct Hk as [<-|Hk]; [ match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?j)) = _ => let z := eval vm_compute in (Z.of_nat j) in
      rewrite !(getr_reg _ j (@BV 5 z I) eq_refl) end; apply K; cbv; tauto |]). destruct Hk.
Qed.
Lemma keeps_but_reg (L : list Prelude.reg) (R R' : bvmap 5 word) k (r : Prelude.reg) : keeps_but L R R' -> bv_unsigned r = Z.of_nat k ->
  In r callee_saved -> ~ In r L -> getr R' (reg k) = getr R (reg k).
Proof. intros K E Hc Hn. rewrite !(getr_reg _ k r E). apply K; assumption. Qed.
(* [comment removed for export] *)
Lemma rdn_img (M : word -> option byte) lo hi a (k : nat) : L5.img_clear M lo hi -> 0 <= lo -> hi <= 2 ^ 64 -> lo <= a -> a + Z.of_nat k <= hi ->
  rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros IC Hlo Hhi Ha Hk. destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]. { replace k with 0%nat by lia. reflexivity. }
  apply rdn_ext; rewrite L5.unsigned_lit by lia; [lia|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. lia.
Qed.
(* [comment removed for export] *)
Lemma u64_of_zeros (M : word -> option byte) a : L5KA.zeros_at M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a 0.
Proof.
  intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
  apply Ba0DiagChk_b.rdn_zeros. rewrite L5.unsigned_lit by lia. cbn. lia.
  intros i Hi. rewrite L5.unsigned_lit by lia. apply Z8. cbn in Hi. lia.
Qed.
Lemma rdn_cons (M : word -> option byte) a (b : byte) (k : nat) l : 0 <= a -> a + 1 + Z.of_nat k <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [b] -> rdn RSEGS M (Z_to_bv 64 (a + 1)) k = Some l -> rdn RSEGS M (Z_to_bv 64 a) (Datatypes.S k) = Some (b :: l).
Proof.
  intros Ha Hk R1 Rk. change (Datatypes.S k) with (1 + k)%nat. change (b :: l) with ([b] ++ l). apply SeqExec.rdn_app; [exact R1|].
  replace ((Z_to_bv 64 a + nat_to_word 1)%bv) with (Z_to_bv 64 (a + 1)); [exact Rk|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma rdn_app_Z (M : word -> option byte) a (n1 n2 : nat) l1 l2 : 0 <= a -> a + Z.of_nat n1 + Z.of_nat n2 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n1 = Some l1 -> rdn RSEGS M (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some l2 -> rdn RSEGS M (Z_to_bv 64 a) (n1 + n2) = Some (l1 ++ l2).
Proof.
  intros Ha Hk R1 R2. apply SeqExec.rdn_app; [exact R1|].
  replace ((Z_to_bv 64 a + nat_to_word n1)%bv) with (Z_to_bv 64 (a + Z.of_nat n1)); [exact R2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
End DK.

(* [comment removed for export] *)
Ltac dk_feed P tac :=
  lazymatch type of P with
  | ?A -> _ =>
      let H := fresh "SC" in
      first [ assert (H : A) by tac | fail 1 "feed: cannot prove premise" A ];
      specialize (P H); clear H; dk_feed P tac
  | _ => idtac
  end.
Ltac dk_gmem :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
  | |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
  | |- L5KA.zeros_at ?M ?a ?n => match goal with H : L5KA.zeros_at M ?b ?m |- _ => apply (L5KA.zeros_at_sub M b m a n H); clear; lia end
  | |- L5.img_clear ?M _ _ => match goal with H : L5.img_clear M _ _ |- _ => exact H end
  end.

(* [comment removed for export] *)
Ltac dk_fpreg_in H :=
  repeat match type of H with context [getr ?R (Z_to_bv 5 (Z.of_nat ?k))] =>
    let z := eval vm_compute in (Z.of_nat k) in rewrite (DK.getr_reg R k (@BV 5 z I) eq_refl) in H end.
Ltac dk_fpreg :=
  repeat match goal with |- context [getr ?R (Z_to_bv 5 (Z.of_nat ?k))] =>
    let z := eval vm_compute in (Z.of_nat k) in rewrite (DK.getr_reg R k (@BV 5 z I) eq_refl) end.
(* [comment removed for export] *)
Ltac dk_kb K :=
  lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    let z := eval vm_compute in (Z.of_nat k) in
    apply (DK.keeps_but_reg _ _ _ k (@BV 5 z I) K eq_refl); [cbv; tauto | cbv; intuition discriminate] end.

(* [comment removed for export] *)
Ltac dk_arith_shape :=
  lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
  end.
Ltac dk_arith_goal := first [ dk_arith_shape | red; dk_arith_shape ].

(* [comment removed for export] *)
Ltac dk_norm H :=
  lazymatch type of H with
  | L5.u64_at _ _ ?a ?v => try (progress (ring_simplify a in H)); try (lazymatch type of H with L5.u64_at _ _ _ ?v' => progress (ring_simplify v' in H) end)
  | L5.u32_at _ _ ?a ?v => try (progress (ring_simplify a in H))
  | L5.u8_at _ _ ?a ?v => try (progress (ring_simplify a in H))
  | getr _ _ = Z_to_bv 64 ?v => try (progress (ring_simplify v in H))
  | _ => idtac
  end.
Ltac dk_split H :=
  lazymatch type of H with
  | _ /\ _ => let A := fresh "Q" in let B := fresh "Q" in destruct H as [A B]; dk_norm A; dk_split B
  | _ => dk_norm H
  end.
Tactic Notation "dk_open" hyp(P) "as" ident(fx) ident(R) ident(M) ident(MG) ident(FR) ident(FZ) ident(MS) ident(KS) :=
  let T := fresh "T" in
  destruct P as (fx & R & M & MG & FR & FZ & (MS & KS & T)); dk_split T.
Ltac dk_exactv H tac :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ _ ?v => lazymatch type of H with L5.u64_at _ _ _ ?vH => replace v with vH by tac; exact H end
          | |- L5.u32_at _ _ _ ?v => lazymatch type of H with L5.u32_at _ _ _ ?vH => replace v with vH by tac; exact H end
          | |- L5.u8_at _ _ _ ?v => lazymatch type of H with L5.u8_at _ _ _ ?vH => replace v with vH by tac; exact H end
          end ].
(* [comment removed for export] *)
Ltac dk_cell_with EXT tac H M Ms a v :=
  match goal with
  | AG : forall x : word, _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
  | AG : forall x : word, _ -> _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
  | AG : forall x : word, _ -> _ -> _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
  end.
Ltac dk_cell tac :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M ?a ?v =>
      try (progress (ring_simplify a)); try (lazymatch goal with |- L5.u64_at _ _ _ ?v1 => progress (ring_simplify v1) end);
      lazymatch goal with |- L5.u64_at _ _ ?a' ?v' =>
        match goal with
        | H : L5.u64_at sg M a' _ |- _ => dk_exactv H tac
        | H : L5.u64_at sg ?Ms a' _ |- _ => dk_cell_with DK.u64_ext tac H M Ms a' v'
        end end
  | |- L5.u32_at ?sg ?M ?a ?v =>
      try (progress (ring_simplify a));
      lazymatch goal with |- L5.u32_at _ _ ?a' ?v' =>
        match goal with
        | H : L5.u32_at sg M a' _ |- _ => exact H
        | H : L5.u32_at sg ?Ms a' _ |- _ => dk_cell_with DK.u32_ext tac H M Ms a' v'
        end end
  | |- L5.u8_at ?sg ?M ?a ?v =>
      try (progress (ring_simplify a));
      lazymatch goal with |- L5.u8_at _ _ ?a' ?v' =>
        match goal with
        | H : L5.u8_at sg M a' _ |- _ => exact H
        | H : L5.u8_at sg ?Ms a' _ |- _ => dk_cell_with DK.u8_ext tac H M Ms a' v'
        end end
  end.
(* [comment removed for export] *)
Ltac dk_greg :=
  lazymatch goal with |- getr ?R ?x = ?rhs =>
    match goal with H : getr R x = ?rhs' |- _ => first [ exact H | (rewrite H; f_equal; lia) ] end end.
(* [comment removed for export] *)
Ltac dk_kept KS :=
  lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    rewrite (KS k) by (apply L5K.in_b; vm_compute; reflexivity) end.

(* [comment removed for export] *)
Ltac dk_xf Ms AG tac :=
  first [ dk_gmem
        | (eapply (DK.u64_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem])
        | (eapply (DK.u32_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem])
        | (eapply (DK.u8_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem]) ].

(* [comment removed for export] *)
Ltac dk_rk :=
  first [ dk_greg
        | match goal with K : forall x, In x _ -> getr ?Rb (Z_to_bv 5 (Z.of_nat x)) = getr _ (Z_to_bv 5 (Z.of_nat x)) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            constr_eq Rb Rb'; rewrite (K k) by (first [apply L5K.in_b; vm_compute; reflexivity | cbn; tauto]); dk_rk end ].

(* [comment removed for export] *)
Ltac dk_qlia := solve [L5FastLia.prune_arith; L5FastLia.lia_ne].

(* [comment removed for export] *)
Ltac dk_export M tac :=
  repeat match goal with
  | H : L5.u64_at ?sg ?Ms ?a ?v |- _ =>
      lazymatch Ms with M => fail | _ => idtac end;
      first [ assert (L5.u64_at sg M a v) by (dk_cell_with DK.u64_ext tac H M Ms a v) | idtac ]; clear H
  | H : L5.u32_at ?sg ?Ms ?a ?v |- _ =>
      lazymatch Ms with M => fail | _ => idtac end;
      first [ assert (L5.u32_at sg M a v) by (dk_cell_with DK.u32_ext tac H M Ms a v) | idtac ]; clear H
  | H : L5.u8_at ?sg ?Ms ?a ?v |- _ =>
      lazymatch Ms with M => fail | _ => idtac end;
      first [ assert (L5.u8_at sg M a v) by (dk_cell_with DK.u8_ext tac H M Ms a v) | idtac ]; clear H
  end.
