(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Export Tac Bytes.

Module DA_Hbsz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Definition cfglen_expr (d0 d1 : byte) : Z :=
  Z.lor (Z.shiftr ((Z.shiftl (bv_unsigned (sxb d1)) 57) mod 18446744073709551616) 49) (bv_unsigned d0).
Definition cfgv (v0 v1 : Z) : Z := (v0 + 256 * v1) mod 32768.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n).
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma Z_to_bv8_bv_unsigned : forall (x : byte), Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Definition hdrv_hi (d1 : byte) : Z := Z.shiftr ((Z.shiftl (bv_unsigned (sxb d1)) 57) mod 18446744073709551616) 49.
Lemma hdrv_hi_tab : forallb (fun v1 => Z.eqb (hdrv_hi (Z_to_bv 8 v1)) (256 * (v1 mod 128))) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cfglen_val : forall d0 d1 : byte, cfglen_expr d0 d1 = cfgv (bv_unsigned d0) (bv_unsigned d1).
Proof.
  intros d0 d1. pose proof (bv_unsigned_in_range _ d0) as R0. pose proof (bv_unsigned_in_range _ d1) as R1.
  unfold bv_modulus in R0, R1. cbn in R0, R1.
  pose proof hdrv_hi_tab as T. rewrite forallb_forall in T.
  specialize (T (bv_unsigned d1) (proj2 (in_zseq 256 (bv_unsigned d1)) ltac:(change (Z.of_nat 256) with 256%Z; lia))). apply Z.eqb_eq in T.
  rewrite Z_to_bv8_bv_unsigned in T.
  change (cfglen_expr d0 d1) with (Z.lor (hdrv_hi d1) (bv_unsigned d0)). rewrite T.
  pose proof (Z.mod_pos_bound (bv_unsigned d1) 128 ltac:(lia)) as HM.
  rewrite Z.lor_comm.
  replace (256 * (bv_unsigned d1 mod 128)) with (Z.shiftl (bv_unsigned d1 mod 128) 8) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  rewrite (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.lor_shiftl8_add (bv_unsigned d0) (bv_unsigned d1 mod 128) R0 ltac:(lia)).
  unfold cfgv.
  pose proof (Z.div_mod (bv_unsigned d1) 128 ltac:(lia)) as DM.
  apply (Z.mod_unique_pos _ _ (bv_unsigned d1 / 128)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma cfgv_range : forall v0 v1, 0 <= cfgv v0 v1 < 32768.
Proof. intros. unfold cfgv. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma cntu_tab : forallb (fun v1 => Bool.eqb (9223372036854775808 <=? bv_unsigned (sxb (Z_to_bv 8 v1))) (128 <=? v1)) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cntu_val : forall d1 : byte, (9223372036854775808 <=? bv_unsigned (sxb d1)) = (128 <=? bv_unsigned d1).
Proof.
  intros d1. pose proof (bv_unsigned_in_range _ d1) as R1. unfold bv_modulus in R1. cbn in R1.
  pose proof cntu_tab as T. rewrite forallb_forall in T.
  specialize (T (bv_unsigned d1) (proj2 (in_zseq 256 (bv_unsigned d1)) ltac:(change (Z.of_nat 256) with 256%Z; lia))).
  apply Bool.eqb_prop in T. rewrite Z_to_bv8_bv_unsigned in T. exact T.
Qed.
End DA_Hbsz.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zeq :=
  first
  [ reflexivity
  | lazymatch goal with
    (* [comment removed for export] *)
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]
    (* [comment removed for export] *)
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq
    (* [comment removed for export] *)
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq | rewrite (Z.eqb_sym a b); f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- negb _ = negb _ => f_equal; zeq
    | |- @eq bool _ _ => zeq_boolarith
    end
  | lia ]
(* [comment removed for export] *)
with unfold1 a := try (is_var a; cbv delta [a])
(* [comment removed for export] *)
with zeq_boolarith :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac zeq_fast :=
  first
  [ reflexivity
  | lazymatch goal with
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- negb _ = negb _ => f_equal; zeq_fast
    | |- @eq bool _ _ => zeq_boolarith_fast
    end
  | slim; lia ]
with zeq_boolarith_fast :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac getreg n :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

(* [comment removed for export] *)
Ltac name_as_tac X e :=
  set (X := e);
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

(* [comment removed for export] *)
Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

(* [comment removed for export] *)
Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
