(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 128 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac slia ::= first [ exact I | lia | repeat split; try exact I; lia ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac sbad_pc t := lazymatch t with Z_to_bv 64 87316 => idtac | Z_to_bv 64 87320 => idtac end.

Ltac sclosed t := assert_fails (idtac; match t with context [?v] => is_var v end).

Ltac sfold :=
  repeat match goal with |- context [Z.land ?x ?y] =>
    sclosed x; sclosed y;
    let v := eval vm_compute in (Z.land x y) in is_Zlit v; change (Z.land x y) with v
  end.

Ltac sres_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then ?T else ?E) _ _ _ _) =>
      sfold;
      tryif sbad_pc T then
        first [ if_false
              | let K := fresh "K" in if_cases K; [zify_cond K; rewrite ?unsigned_lit_wrap in K; exfalso; lia | clear K]
              | fail "sres_if: taken branch is the stop" ]
      else tryif sbad_pc E then
        first [ if_true
              | let K := fresh "K" in if_cases K; [clear K | zify_cond K; rewrite ?unsigned_lit_wrap in K; exfalso; lia]
              | fail "sres_if: fallthrough is the stop" ]
      else
        first [ if_true
              | if_false
              | let K := fresh "K" in if_cases K; [zify_cond K; rewrite ?unsigned_lit_wrap in K; exfalso; lia | clear K]
              | let K := fresh "K" in if_cases K; [clear K | zify_cond K; rewrite ?unsigned_lit_wrap in K; exfalso; lia]
              | fail "sres_if: undetermined" ]
  | _ => idtac
  end.

Ltac zr_until a :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 a) _ _ _ _) => idtac
  | _ => zstep; sres_if; zr_until a
  end.

Lemma bytes_at_byte1 : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.
