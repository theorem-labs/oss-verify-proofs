(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OSSVerify.Proofs.openssl.ct.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition al8 (x : Z) : Prop := x mod 8 = 0.
Definition al16 (x : Z) : Prop := x mod 16 = 0.
Definition al4 (x : Z) : Prop := x mod 4 = 0.

Lemma al8_intro : forall x, x mod 8 = 0 -> al8 x. Proof. intros x H. exact H. Qed.
Lemma al8_elim : forall x, al8 x -> x mod 8 = 0. Proof. intros x H. exact H. Qed.
Lemma al16_intro : forall x, x mod 16 = 0 -> al16 x. Proof. intros x H. exact H. Qed.
Lemma al8_of_al16 : forall x, al16 x -> al8 x.
Proof. unfold al8, al16. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma al8_add : forall x k, al8 x -> k mod 8 = 0 -> al8 (x + k).
Proof. unfold al8. intros x k H K. Z.div_mod_to_equations. lia. Qed.
Lemma al16_add : forall x k, al16 x -> k mod 16 = 0 -> al16 (x + k).
Proof. unfold al16. intros x k H K. Z.div_mod_to_equations. lia. Qed.
Lemma al8_lit : forall x, ((x mod 8) =? 0) = true -> al8 x.
Proof. intros x H. apply Z.eqb_eq in H. exact H. Qed.

(* [comment removed for export] *)
Ltac ual :=
  repeat match goal with
         | H : context [(?x mod 16 = 0)%Z] |- _ => change ((x mod 16 = 0)%Z) with (al16 x) in H
         | H : context [(?x mod 8 = 0)%Z] |- _ => change ((x mod 8 = 0)%Z) with (al8 x) in H
         | H : context [(?x mod 4 = 0)%Z] |- _ => change ((x mod 4 = 0)%Z) with (al4 x) in H
         end.
(* [comment removed for export] *)
Ltac ulia_open := unfold al4, al8, al16 in *.

(* [comment removed for export] *)
Lemma usx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bn_swrap32_small. lia. Qed.
Lemma uzx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma uswrap32_ulit : forall z, 0 <= z < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z)) = z.
Proof. intros z Hz. rewrite unsigned_lit by lia. apply bn_swrap32_small. lia. Qed.
Lemma uwrap32_ulit : forall z, 0 <= z < 2^32 -> bv_wrap 32 (bv_unsigned (Z_to_bv 64 z)) = z.
Proof. intros z Hz. rewrite unsigned_lit by lia. unfold bv_wrap, bv_modulus. apply Z.mod_small. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. lia. Qed.
Lemma umod32_ulit : forall z, 0 <= z < 2^32 -> (bv_unsigned (Z_to_bv 64 z) mod 4294967296 = z)%Z.
Proof. intros z Hz. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Ltac usmall C := repeat (rewrite uswrap32_ulit in C by lia); repeat (rewrite uwrap32_ulit in C by lia); repeat (rewrite umod32_ulit in C by lia);
                rewrite ?usx32_small, ?uzx32_small in C by lia;
                repeat (rewrite Z.shiftl_mul_pow2 in C by lia);          (* [comment removed for export] *)
                repeat (rewrite ZBridge.zb_lxor_ones in C by lia).      (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac uchk_open := unfold al4, al8, al16, ub_ptr_ok in *.
Ltac uchk_solve C :=
  first [ solve [clear - C; lia]
        | solve [rewrite ?unsigned_lit in C by lia; lia]
        | solve [usmall C; rewrite ?unsigned_lit in C by lia; lia]
        | solve [uchk_open; try usmall C; ub_norm C; first [ ub_solve C | ub_ltb_cases C ]] ].

(* [comment removed for export] *)
Ltac uchk :=
  zstep; ub_sw; ub_lts;
  first [ ub_pc_lit | if_false
        | let C := fresh "Cub" in
          if_cases C; [ exfalso; zify_cond C; first [ uchk_solve C | fail 100 "uchk: cannot refute the UBSan trap condition" ] | clear C ] ].

(* [comment removed for export] *)
Ltac ub1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ uchk | fail 100 "ub: cannot refute the UBSan trap condition at pc" pc ]
      end
  end.
Ltac ub := repeat ub1.

(* [comment removed for export] *)
Ltac has_var c := match c with context [?x] => is_var x end.
Ltac udecide :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ (tryif has_var c then fail else
               (let v := eval vm_compute in c in
                lazymatch v with
                | true => replace c with true by (vm_compute; reflexivity); cbv iota
                | false => replace c with false by (vm_compute; reflexivity); cbv iota
                end))
            | if_false | if_true
            | (let C := fresh "Cub" in if_cases C; [ exfalso; zify_cond C; uchk_solve C | clear C ])
            | (let C := fresh "Cub" in if_cases C; [ clear C | exfalso; zify_cond C; uchk_solve C ]) ]
  end.
(* [comment removed for export] *)
Ltac upre := ual; ub; try (udecide; ub).


(* [comment removed for export] *)
Lemma al16_frame : forall s k, al16 s -> (k mod 16 = 0)%Z -> (0 <= s - k)%Z -> (s - k < 18446744073709551616)%Z ->
  (bv_unsigned (Z_to_bv 64 (s + - k)) mod 16 = 0)%Z.
Proof.
  intros s k H K R1 R2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  unfold al16 in H. Z.div_mod_to_equations. lia.
Qed.
Lemma al16_shift : forall s k, al16 s -> (k mod 16 = 0)%Z -> ((s + k) mod 16 = 0)%Z.
Proof. intros s k H K. unfold al16 in H. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Ltac ualign := uchk_open; repeat (rewrite unsigned_lit by lia); Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac uand7 H :=
  zstep;
  lazymatch type of H with
  | al8 ?p => first [ rewrite (land7 p H) | rewrite (land7_wrap p H) | idtac ]
  | (?p mod 8 = 0)%Z => first [ rewrite (land7 p H) | rewrite (land7_wrap p H) | idtac ]
  end.

(* [comment removed for export] *)
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc | |- _ => idtac "(no machine state)" end.
