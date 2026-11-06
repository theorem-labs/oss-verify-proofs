(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2KU.
Import L5CSU L5PSU L5STRKU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac keep_arith := lazymatch goal with |- _ => L5FastLia.prune_arith end; repeat match goal with H : Z.modulo _ _ = _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac alia0 := keep_arith; clear_disj; lia.
Ltac alia1 := keep_arith;
  first [ solve [ clear_disj; lia ]
        | match goal with H : _ \/ _ |- _ => solve [ generalize H; clear_disj; intros; lia ] end ].
Ltac alia := keep_arith;
  first [ solve [ clear_disj; lia ]
        | match goal with H : _ \/ _ |- _ => solve [ generalize H; clear_disj; intros; lia ] end
        | match goal with H1 : _ \/ _ |- _ => match goal with H2 : _ \/ _ |- _ => solve [ generalize H1 H2; clear_disj; intros; lia ] end end ].
(* [comment removed for export] *)
Ltac alia3 := keep_arith; lia.
Section SCFG_2.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition ZERO_THROW : Z := 0x22c00.   (* [comment removed for export] *)
Definition AALLOC_RET : Z := 0x3fee0.   (* [comment removed for export] *)
Definition DIV_CTOR : Z := 0x22c20.     (* [comment removed for export] *)
Definition MALLOC_RET : Z := 0x5abc8.   (* [comment removed for export] *)
Definition THROW2 : Z := 0x22c38.       (* [comment removed for export] *)
Definition PAD1 : Z := 0x22c50.         (* [comment removed for export] *)
Definition RESUME1 : Z := 0x22d28.      (* [comment removed for export] *)
Definition PAD2 : Z := 0x224c8.         (* [comment removed for export] *)
Definition RESUME2 : Z := 0x224f0.      (* [comment removed for export] *)
Definition TOP_PAD : Z := 0x209b4.      (* [comment removed for export] *)
Definition OPMOD1_RET : Z := 0x20854.   (* [comment removed for export] *)
Definition DIV_RET : Z := 0x22494.      (* [comment removed for export] *)

Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).

(* [comment removed for export] *)
Definition OPEQ_RET : Z := 0x20d10.     (* [comment removed for export] *)
Definition frame2 (R0 : bvmap 5 word) (S fden : Z) (M : word -> option byte) : Prop :=
     L5.u64_at RSEGS M (S - 72) DIV_RET /\ L5.u64_at RSEGS M (S - 80) (S + 64)
  /\ L5.u64_at RSEGS M (S - 88) (U R0 9) /\ L5.u64_at RSEGS M (S - 96) (U R0 18) /\ L5.u64_at RSEGS M (S - 104) (U R0 19)
  /\ L5.u64_at RSEGS M (S - 112) (U R0 20) /\ L5.u64_at RSEGS M (S - 120) (U R0 21) /\ L5.u64_at RSEGS M (S - 128) (U R0 22)
  /\ L5.u64_at RSEGS M (S - 136) (U R0 23) /\ L5.u64_at RSEGS M (S - 144) (U R0 24) /\ L5.u64_at RSEGS M (S - 152) (U R0 25)
  /\ L5.u64_at RSEGS M (S - 160) (U R0 26) /\ L5.u64_at RSEGS M (S - 168) (U R0 27)
  /\ L5.u8_at RSEGS M (S - 200) fden
  /\ L5.u8_at RSEGS M (S - 64) 0.
(* [comment removed for export] *)
Definition frame2_top (R0 : bvmap 5 word) (S : Z) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 32) (S + 96) /\ L5.u64_at RSEGS M (S - 24) OPEQ_RET /\ L5.u64_at RSEGS M (S - 16) (U R0 8) /\ L5.u64_at RSEGS M (S - 8) OPMOD1_RET.

Lemma frame2_agree R0 S fden M M' : L5C.agree_on M M' (S - 200) 144 -> 2 ^ 40 <= S -> S <= 2 ^ 47 -> frame2 R0 S fden M -> frame2 R0 S fden M'.
Proof.
  intros AG LO HI F. unfold frame2 in *. decompose [and] F.
  repeat match goal with |- _ /\ _ => split end;
  first [ eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | assumption]
        | eapply L5C.u8_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | assumption] ].
Qed.
Lemma frame2_top_agree R0 S M M' : L5C.agree_on M M' (S - 32) 32 -> 2 ^ 40 <= S -> S <= 2 ^ 47 -> frame2_top R0 S M -> frame2_top R0 S M'.
Proof.
  intros AG LO HI (A & B & C & D). repeat split;
  (eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | eassumption]).
Qed.

(* [comment removed for export] *)
Definition exc2_obj (M : word -> option byte) (obj ref : Z) : Prop :=
     (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M (obj - 128 + i) 0)
  /\ (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M (obj - 80 + i) 0)
  /\ L5.u64_at RSEGS M obj L5USU.VT_RUNTIME_ERROR /\ L5.u64_at RSEGS M (obj + 8) (ref + 24)
  /\ L5USU.refstring_at M ref L5USU.zero_divide_msg.

Lemma exc2_obj_agree M M' obj ref :
  L5C.agree_on M M' (obj - 128) 8 -> L5C.agree_on M M' (obj - 80) 12 -> L5C.agree_on M M' obj 16 -> L5C.agree_on M M' ref 37 ->
  4096 <= obj - 128 -> obj + 16 <= 2 ^ 47 -> 4096 <= ref -> ref + 37 <= 2 ^ 47 ->
  exc2_obj M obj ref -> exc2_obj M' obj ref.
Proof.
  intros AG1 AG2 AG3 AG4 O1 O2 R1 R2 (Z8 & Z12 & VT & IMP & RS). unfold exc2_obj.
  split. { intros i Hi. eapply L5C.u8_at_agree; [eapply L5C.agree_on_sub; [exact AG1 | lia | lia] | lia | lia | apply Z8; lia]. }
  split. { intros i Hi. eapply L5C.u8_at_agree; [eapply L5C.agree_on_sub; [exact AG2 | lia | lia] | lia | lia | apply Z12; lia]. }
  split. { eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG3 | lia | lia] | lia | lia | exact VT]. }
  split. { eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG3 | lia | lia] | lia | lia | exact IMP]. }
  eapply L5USU.refstring_at_agree; [| lia | | exact RS]; unfold L5USU.zero_divide_msg; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [| lia].
  eapply L5C.agree_on_sub; [exact AG4 | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma refstring_of_cells M ref :
  4096 <= ref -> ref + 37 <= 2 ^ 47 ->
  L5.u64_at RSEGS M (ref + 0) 12 -> L5.u64_at RSEGS M (ref + 8) 12 -> L5.u32_at RSEGS M (ref + 16) 0 ->
  L5.u64_at RSEGS M (ref + 24) 8532461059501614426 ->
  L5.u8_at RSEGS M (ref + 32) 105 -> L5.u8_at RSEGS M (ref + 33) 100 -> L5.u8_at RSEGS M (ref + 34) 101 -> L5.u8_at RSEGS M (ref + 35) 46 ->
  L5.u8_at RSEGS M (ref + 36) 0 ->
  L5USU.refstring_at M ref L5USU.zero_divide_msg.
Proof.
  intros LO HI W0 W8 W16 W24 B32 B33 B34 B35 B36. unfold L5USU.refstring_at, L5USU.zero_divide_msg. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ app].
  split. rewrite Z.add_0_r in W0. exact W0. split. exact W8. split. exact W16.
  assert (J13: rdn RSEGS M (Z_to_bv 64 (ref + 24)) 13 = Some (word_to_le_bytes 8 (Z_to_bv 64 8532461059501614426) ++ [Z_to_bv 8 105] ++ [Z_to_bv 8 100] ++ [Z_to_bv 8 101] ++ [Z_to_bv 8 46] ++ [Z_to_bv 8 0])).
  { change 13%nat with (8 + (1 + (1 + (1 + (1 + 1)))))%nat. apply (L5B.rdn_join RSEGS M 8). lia. lia. exact W24.
    replace (ref + 24 + Z.of_nat 8) with (ref + 32) by lia. apply (L5B.rdn_join RSEGS M 1). lia. lia. exact B32.
    replace (ref + 32 + Z.of_nat 1) with (ref + 33) by lia. apply (L5B.rdn_join RSEGS M 1). lia. lia. exact B33.
    replace (ref + 33 + Z.of_nat 1) with (ref + 34) by lia. apply (L5B.rdn_join RSEGS M 1). lia. lia. exact B34.
    replace (ref + 34 + Z.of_nat 1) with (ref + 35) by lia. apply (L5B.rdn_join RSEGS M 1). lia. lia. exact B35.
    replace (ref + 35 + Z.of_nat 1) with (ref + 36) by lia. exact B36. }
  pose proof (L5C.rdn_bytes_at RSEGS M (word_to_le_bytes 8 (Z_to_bv 64 8532461059501614426) ++ [Z_to_bv 8 105] ++ [Z_to_bv 8 100] ++ [Z_to_bv 8 101] ++ [Z_to_bv 8 46] ++ [Z_to_bv 8 0]) (ref + 24) ltac:(lia) ltac:(cbn; lia) J13) as BY.
  replace (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 8532461059501614426) ++ [Z_to_bv 8 105] ++ [Z_to_bv 8 100] ++ [Z_to_bv 8 101] ++ [Z_to_bv 8 46] ++ [Z_to_bv 8 0]))
     with [90; 101; 114; 111; 32; 100; 105; 118; 105; 100; 101; 46; 0] in BY by (vm_compute; reflexivity).
  exact BY.
Qed.

(* [comment removed for export] *)
Lemma statics_landed_keep M M' gd av uid rnd canary hw :
  L5USU.statics_landed M gd av uid rnd canary hw -> (forall a, stat_rd av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5USU.statics_landed M' gd av uid rnd canary hw.
Proof.
  intros ST K. unfold L5USU.statics_landed in *.
  unfold stat_rd, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in *.
  decompose [and] ST.
  assert (AG: forall a n, (forall i, a <= i < a + n -> (459768 <= i < 459768 + 12) \/ (460320 <= i < 460320 + 2) \/ (462433 <= i < 462433 + 6) \/
     (462600 <= i < 462600 + 8) \/ (594472 <= i < 594472 + 8) \/ (594344 <= i < 594344 + 8) \/ (594384 <= i < 594384 + 8) \/
     (av <= i < av + 160) \/ (0x10000 <= i < 0x60100) \/ (0x60128 <= i < 0x60148) \/ (0x60158 <= i < 0x60160)) -> L5C.agree_on M M' a n).
  { intros a n Hn i Hi. apply K. apply Hn. exact Hi. }
  repeat match goal with |- _ /\ _ => split end;
  first [ eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
        | eapply L5USU.u32_at_agree; [apply AG; intros; lia | lia | lia | assumption]
        | eapply (L5C.u8_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
        | assumption
        | intros j Hj; eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | auto]
        | intros i Hi; rewrite K by lia; auto ].
Qed.

(* [comment removed for export] *)
Lemma land254_bit0 fb : 0 <= fb < 256 -> Z.testbit fb 0 = false -> Z.land fb 254 = fb.
Proof.
  intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite B0. reflexivity. }
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - replace (Z.testbit 254 i) with true. apply Bool.andb_true_r.
    assert (Hc : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; reflexivity.
  - assert (Z.testbit fb i = false) as ->.
    { apply Z.testbit_false. lia. rewrite Z.div_small. reflexivity. split. lia.
      apply Z.lt_le_trans with (2 ^ 8). lia. apply Z.pow_le_mono_r; lia. }
    reflexivity.
Qed.

Lemma exc2_at_agree M M' obj ref cfa :
  L5C.agree_on M M' (obj - 128) 144 -> L5C.agree_on M M' ref 37 ->
  4096 <= obj - 128 -> obj + 16 <= 2 ^ 47 -> 4096 <= ref -> ref + 37 <= 2 ^ 47 ->
  L5USU.exc2_at M obj ref cfa -> L5USU.exc2_at M' obj ref cfa.
Proof.
  intros AGO AGR O1 O2 R1 R2 (HDR & VT & IMP & RS). split; [| split; [| split]].
  - eapply L5USU.exc_hdr_agree; [exact AGO | lia | lia | exact HDR].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact VT].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact IMP].
  - eapply L5USU.refstring_at_agree; [| lia | | exact RS]; unfold L5USU.zero_divide_msg; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [| lia].
    eapply L5C.agree_on_sub; [exact AGR | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma hull_lo_eq : L5.hull_lo RSEGS = 0x10000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_hi_eq : L5.hull_hi RSEGS = 0x92000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_of a n : (a + n <= 0x10000 \/ 0x92000 <= a) -> L5.hull_apart RSEGS a n.
Proof. intros H. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. exact H. Qed.

(* [comment removed for export] *)
Lemma u32_zero_of_bytes M a :
  (forall i, 0 <= i < 4 -> L5.u8_at RSEGS M (a + i) 0) -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a 0.
Proof.
  intros Z4 Ha Hn. unfold L5.u32_at.
  assert (J: rdn RSEGS M (Z_to_bv 64 a) 4 = Some ([Z_to_bv 8 0] ++ [Z_to_bv 8 0] ++ [Z_to_bv 8 0] ++ [Z_to_bv 8 0])).
  { change 4%nat with (1 + (1 + (1 + 1)))%nat. apply (L5B.rdn_join RSEGS M 1). lia. lia. replace a with (a + 0) at 1 by lia. apply Z4. lia.
    apply (L5B.rdn_join RSEGS M 1). lia. lia. replace (a + Z.of_nat 1) with (a + 1) by lia. apply Z4. lia.
    replace (a + Z.of_nat 1 + Z.of_nat 1) with (a + 2) by lia. apply (L5B.rdn_join RSEGS M 1). lia. lia. apply Z4. lia.
    replace (a + 2 + Z.of_nat 1) with (a + 3) by lia. apply Z4. lia. }
  rewrite J. f_equal.
Qed.

Lemma wseg_caught : wseg_ok RSEGS (Z_to_bv 64 EH_CAUGHT) 8 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lor1_land254_bit1 fb : 0 <= fb < 256 -> Z.testbit fb 0 = true -> Z.lor (Z.land fb 254) 1 = fb.
Proof.
  intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite B0. reflexivity. }
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.orb_false_r.
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - replace (Z.testbit 254 i) with true. apply Bool.andb_true_r.
    assert (Hc : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; reflexivity.
  - assert (Z.testbit fb i = false) as ->.
    { apply Z.testbit_false. lia. rewrite Z.div_small. reflexivity. split. lia.
      apply Z.lt_le_trans with (2 ^ 8). lia. apply Z.pow_le_mono_r; lia. }
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refstring3_of_cells M ref :
  4096 <= ref -> ref + 66 <= 2 ^ 47 ->
  L5.u64_at RSEGS M ref 41 -> L5.u64_at RSEGS M (ref + 8) 41 -> L5.u32_at RSEGS M (ref + 16) 0 ->
  L5.u64_at RSEGS M (ref + 24) 8028075845441778529 -> L5.u64_at RSEGS M (ref + 32) 7863351059373564014 ->
  L5.u64_at RSEGS M (ref + 40) 2838809733452757089 -> L5.u64_at RSEGS M (ref + 48) 2334102023183623712 ->
  L5.u64_at RSEGS M (ref + 56) 4188416081412519009 -> L5.u8_at RSEGS M (ref + 64) 48 -> L5.u8_at RSEGS M (ref + 65) 0 ->
  L5USU.refstring_at M ref L5USU.assert_msg.
Proof.
  intros LO HI W0 W8 W16 A B Cc D E F G. unfold L5USU.refstring_at, L5USU.assert_msg. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ app].
  split. exact W0. split. exact W8. split. exact W16.
  set (bs := word_to_le_bytes 8 (Z_to_bv 64 8028075845441778529) ++ word_to_le_bytes 8 (Z_to_bv 64 7863351059373564014) ++
             word_to_le_bytes 8 (Z_to_bv 64 2838809733452757089) ++ word_to_le_bytes 8 (Z_to_bv 64 2334102023183623712) ++
             word_to_le_bytes 8 (Z_to_bv 64 4188416081412519009) ++ [Z_to_bv 8 48] ++ [Z_to_bv 8 0]).
  assert (J: rdn RSEGS M (Z_to_bv 64 (ref + 24)) 42 = Some bs).
  { subst bs. change 42%nat with (8 + (8 + (8 + (8 + (8 + (1 + 1))))))%nat.
    apply (L5B.rdn_join RSEGS M 8). lia. lia. exact A. replace (ref + 24 + Z.of_nat 8) with (ref + 32) by lia.
    apply (L5B.rdn_join RSEGS M 8). lia. lia. exact B. replace (ref + 32 + Z.of_nat 8) with (ref + 40) by lia.
    apply (L5B.rdn_join RSEGS M 8). lia. lia. exact Cc. replace (ref + 40 + Z.of_nat 8) with (ref + 48) by lia.
    apply (L5B.rdn_join RSEGS M 8). lia. lia. exact D. replace (ref + 48 + Z.of_nat 8) with (ref + 56) by lia.
    apply (L5B.rdn_join RSEGS M 8). lia. lia. exact E. replace (ref + 56 + Z.of_nat 8) with (ref + 64) by lia.
    apply (L5B.rdn_join RSEGS M 1). lia. lia. exact F. replace (ref + 64 + Z.of_nat 1) with (ref + 65) by lia. exact G. }
  pose proof (L5C.rdn_bytes_at RSEGS M bs (ref + 24) ltac:(lia) ltac:(subst bs; cbn; lia) J) as BY.
  replace (map bv_unsigned bs) with [97;115;115;101;114;116;105;111;110;32;39;110;32;60;32;109;97;120;95;115;105;122;101;39;32;102;97;105;108;101;100;32;97;116;32;32;60;62;32;58;48;0] in BY by (subst bs; vm_compute; reflexivity).
  exact BY.
Qed.

End SCFG_2.
End L5E2KU.
