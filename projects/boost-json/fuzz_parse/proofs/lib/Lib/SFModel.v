(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export Walk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Export SoftFloat.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq46Stdlib6ZArith6BinInt1Zj53addj54landj53lorj53subj56moduloj53pow04Npos35stdpp9bitvectorbdefinitionsnb7Z_to_bvj52lenb2bvhc3andj52ltj53oppnb9bv_signed" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.


Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Notation W64 := 18446744073709551615%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma lor_disjoint_add : ltac2:(zQ "50!h9!j0!kd!l3!la>1a$0>1b$0>0@3$1$0@2$3^2^1Z@3$1$0@2$4^3^2@2$2^3^2").
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

(* [comment removed for export] *)
Lemma land_even_mask : ltac2:(zQ "40!l3!h9!j0!m0>1y$1@3$2$1@2$0^1+vvvvvvvvvvvvvvve@2$3@2$0^1+vvvvvvvvvvvvvvvf@2$0^1+1").
Proof.
  intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
  rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
  rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
  rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : ltac2:(zQ "40!h9!j0!l3!m6>1y$0@3$1$0@2$2^1+1@2$3^1+2").
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : ltac2:(zQ "50!h9!j0!l3!m6!mf>1y$0@3$1$0@2$2^1+vvvvvvvvvvvvvvvf@2$3^1@2$4+2+k0").
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : ltac2:(zQ "80!n5!kd!l3!p8!j0!h9!q2!q7>1x$5>0@2$6Z^1@3$4@1$7@1$0#k0@2$3@1$0#k0@2$2@2$1^2+1+vvvvvvvvvvvvvvve@2$3@1$0#k0@2$1^2@2$2^2+1").
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, land_W64, !land_1.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bool_atom_cases :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
  end.

(* [comment removed for export] *)
Ltac weq :=
  first [ reflexivity
        | f_equal; zeq
        | rewrite round_even_idiom by zrange_nonneg; weq_arith
        | weq_arith ]
with weq_arith :=
  apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
  bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac ms_eq :=
  first [ reflexivity
        | lazymatch goal with
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
          | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
          | |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
          | |- context [mkR] => unfold mkR; ms_eq
          | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
          | |- Some _ = Some _ => f_equal; ms_eq
          end ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma signed_of_Z : ltac2:(zQ "a0!n5!h9!mf!qc!j0!q2!r2!r7!p8!rd>1z$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma mod64_land63 : ltac2:(zQ "40!h9!j0!l3!m6>1y$0@3$1$0@2$3^1+k0@2$2^1+jf").
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : ltac2:(zQ "30!l3!h9!j0>1y$1@3$2$1@2$0@2$0^1+jf+jf@2$0^1+jf").
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  | |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
  end.
Ltac zs_idioms_sf_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  | context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
  end.
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
(* [comment removed for export] *)
