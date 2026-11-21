(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma swrap32_small : forall e, -2147483648 <= e < 2147483648 -> bv_swrap 32 e = e.
Proof.
  intros e H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma swrap32_shift : forall e k, bv_swrap 32 (e + 4294967296 * k) = bv_swrap 32 e.
Proof.
  intros e k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  replace (e + 4294967296 * k + 2147483648) with (e + 2147483648 + k * 4294967296) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sx32_small : forall e, 0 <= e < 2147483648 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e H. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity.
Qed.
Lemma sx32_sint : forall e, -2147483648 <= e < 2147483648 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e H. destruct (Z_lt_le_dec e 0) as [N|P]; [| apply sx32_small; lia].
  unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (e mod 18446744073709551616) with (e + 4294967296 * 4294967296) by (Z.div_mod_to_equations; lia).
  rewrite swrap32_shift. rewrite swrap32_small by lia. reflexivity.
Qed.
Lemma swrap32_sublit : forall e k, -2147483648 <= e - k < 2147483648 ->
  bv_swrap 32 (e + (18446744073709551616 - k)) = e - k.
Proof.
  intros e k H. replace (e + (18446744073709551616 - k)) with (e - k + 4294967296 * 4294967296) by lia.
  rewrite swrap32_shift. apply swrap32_small. exact H.
Qed.

Ltac show_pc := lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg n := let w := getreg n in idtac "x" n "=" w.

Ltac show_mkR :=
  let r1 := getreg 1 in let r2 := getreg 2 in let r3 := getreg 3 in let r4 := getreg 4 in let r5 := getreg 5 in
  let r6 := getreg 6 in let r7 := getreg 7 in let r8 := getreg 8 in let r9 := getreg 9 in let r10 := getreg 10 in
  let r11 := getreg 11 in let r12 := getreg 12 in let r13 := getreg 13 in let r14 := getreg 14 in let r15 := getreg 15 in
  let r16 := getreg 16 in let r17 := getreg 17 in let r18 := getreg 18 in let r19 := getreg 19 in let r20 := getreg 20 in
  let r21 := getreg 21 in let r22 := getreg 22 in let r23 := getreg 23 in let r24 := getreg 24 in let r25 := getreg 25 in
  let r26 := getreg 26 in let r27 := getreg 27 in let r28 := getreg 28 in let r29 := getreg 29 in let r30 := getreg 30 in
  let r31 := getreg 31 in
  idtac "(mkR" "(" r1 ") (" r2 ") (" r3 ") (" r4 ") (" r5 ") (" r6 ") (" r7 ") (" r8 ") (" r9 ") (" r10 ") (" r11 ") (" r12 ") (" r13 ") ("
        r14 ") (" r15 ") (" r16 ") (" r17 ") (" r18 ") (" r19 ") (" r20 ") (" r21 ") (" r22 ") (" r23 ") (" r24 ") (" r25 ") ("
        r26 ") (" r27 ") (" r28 ") (" r29 ") (" r30 ") (" r31 "))".

Ltac pose_word_range w :=
  let R := fresh "RW" in
  pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R;
  change (2 ^ Z.of_N 64) with 18446744073709551616 in R.

Ltac at_free_pc STOPS :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) STOPS) in
      lazymatch b with false => idtac | true => fail "stop pc" end
  end.

Ltac closed_w w :=
  lazymatch w with
  | Z_to_bv _ ?x => is_Zlit x
  | sxb ?b => closed_w b
  | zxb ?b => closed_w b
  | zx32 ?b => closed_w b
  | sx32 ?b => closed_w b
  end.
Ltac closed_cond c :=
  lazymatch c with
  | negb ?c' => closed_cond c'
  | bv_eqb ?a ?b => closed_w a; closed_w b
  | bv_ltu ?a ?b => closed_w a; closed_w b
  | bv_lts ?a ?b => closed_w a; closed_w b
  end.
Ltac pc_lit :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      closed_cond c;
      let v := eval vm_compute in c in
      lazymatch v with
      | true => change (if c then a else b) with a
      | false => change (if c then a else b) with b
      end
  end.
Ltac fix_neg_store :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      is_Zlit z; let z' := eval vm_compute in (z mod 18446744073709551616) in
      change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z']; mem_after_store
  | _ => idtac
  end.
Definition nz_tried (e : Z) : Prop := True.
Definition nz_run : Prop := True.
Ltac nz_fresh e := lazymatch goal with _ : nz_tried e |- _ => fail | _ => idtac end.
Ltac nz_mark e := lazymatch goal with _ : nz_run |- _ => let H := fresh "NZT" in assert (H : nz_tried e) by exact I end.
Ltac nz_stop := repeat match goal with H : nz_tried _ |- _ => clear H | H : nz_run |- _ => clear H end.
Ltac nz_start := nz_stop; let H := fresh "NZR" in assert (H : nz_run) by exact I.
Ltac znorm_lia := lia1.
Ltac znorm :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] =>
      nz_fresh e; first [ rewrite (sx32_small e) by znorm_lia | rewrite (sx32_sint e) by znorm_lia | nz_mark e ]
  | |- context [bv_swrap 32 (?e + ?l)] =>
      is_Zlit l;
      let big := eval vm_compute in (9223372036854775808 <=? l) in
      lazymatch big with true => idtac end;
      nz_fresh (e + l);
      first [ let k := eval vm_compute in (18446744073709551616 - l) in
              change l with (18446744073709551616 - k); rewrite (swrap32_sublit e k) by znorm_lia
            | nz_mark (e + l) ]
  | |- context [bv_swrap 32 ?e] => nz_fresh e; first [ rewrite (swrap32_small e) by znorm_lia | nz_mark e ]
  end.
Ltac forget_reg r := let v := reg_val r in let w := fresh "fw" in remember v as w eqn:EW in |- *; clear EW.

Ltac zsubs :=
  repeat match goal with
  | |- context [?a + Zneg ?p] => replace (a + Zneg p) with (a - Zpos p) by lia
  end.
Ltac zs := zstep; fix_neg_store; znorm; try pc_lit.

Definition pcd_live (c : bool) : Prop := True.
Ltac pcd_clear := repeat match goal with H : pcd_live _ |- _ => clear H end.
Ltac pc_dec :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      lazymatch goal with _ : pcd_live c |- _ => fail | _ => idtac end;
      first [ replace (if c then a else b) with a
                by (let K := fresh "K" in destruct c eqn:K; [reflexivity | exfalso; zify_cond K; lia])
            | replace (if c then a else b) with b
                by (let K := fresh "K" in destruct c eqn:K; [exfalso; zify_cond K; lia | reflexivity])
            | let H := fresh "PCDL" in assert (H : pcd_live c) by exact I ]
  end.

Ltac zbr_tac K :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch goal with
      | H : ?T |- _ =>
          lazymatch T with
          | pcd_live c => clear H; if_cases K; zify_cond K
          | _ => pcd_clear; if_cases K; zify_cond K; try (exfalso; lia)
          end
      | _ => if_cases K; zify_cond K; try (exfalso; lia)
      end
  end.
Tactic Notation "zbr" ident(K) := zbr_tac K.
Tactic Notation "zbr0" ident(K) := pcd_clear; if_cases K; zify_cond K.

Ltac zrun STOPS := nz_start; repeat (at_free_pc STOPS; zs); nz_stop.
Ltac zrunb STOPS := nz_start; pcd_clear; repeat (first [ at_free_pc STOPS; zs | pc_dec ]); nz_stop.
Ltac zrun_n N STOPS := nz_start; do N (try (at_free_pc STOPS; zs)); nz_stop.

Ltac tlia ::= first [ zify_noeuclid; xlia zchecker
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

Ltac alia_e := acc_enrich; lia.
Ltac solve_acc_with_c CL H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); CL
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); CL
      end
  end.
Ltac solve_acc_pref CL :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      first [ match goal with
              | H : rng RNG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with_c CL H
              end
            | is_var X;
              match goal with
              | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with_c CL H
              end
            | lazymatch X with bv_unsigned ?r => is_var r;
                match goal with
                | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with_c CL H
                end
              end ]
  end.
Ltac solve_acc_blind CL :=
  first [ lazymatch goal with
          | |- acc_in ?RNG _ =>
              match goal with
              | H : rng RNG _ _ |- _ => solve_acc_with_c CL H
              end
          end
        |
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
              let nz := eval cbv in (Z.of_nat n) in
              match goal with
              | H : rng RNG ?lo ?len |- _ => apply (rng_acc_wrapZ RNG lo len E n nz H (@eq_refl Z nz)); CL
              end
          end ].
Ltac solve_acc_search CL := first [ solve_acc_pref CL | solve_acc_blind CL ].
Ltac solve_acc1 ::=
  first [ acc_hint
        | sassumption
        | lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
              is_closed_lits E;
              match goal with
              | H : rng RNG ?lo ?len |- _ => is_closed_lits lo; is_closed_lits len; solve_acc_lit H
              end
          end
        | solve_acc_pref lia1
        | solve_acc_pref lia
        | solve_acc_blind lia1
        | solve_acc_blind lia
        | solve_acc_search alia_e
        | assumption
        | lazymatch goal with |- acc_in _ (?a, ?n) => fail 0 "footprint: access" a "width" n "not covered by any [rng] hypothesis" end ].

Ltac flia ::= first [ sassumption | progress slim; lia | lia | assumption ].

Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

Ltac ck_join n okpc :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let H := fresh "CONT" in
      enough (H : forall y : word, evtF segs RNG Q (MS (tset p y R) F (Z_to_bv 64 okpc) fc rv m ro));
      [ | let y := fresh "y" in intros y;
          let g := lazymatch goal with |- ?g => g end in
          let g' := eval cbv beta iota delta [tset mkR] in g in change g' ]
  end.

Ltac ck_doneJ n okpc :=
  repeat (lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              let b := eval vm_compute in (Z.eqb pc okpc) in
              lazymatch b with false => zstep | true => fail end
          end);
  lazymatch goal with
  | CONT : forall y : word, evtF _ _ _ _ |- _ => let v := reg_val n in exact (CONT v)
  end.

Ltac ck_branchJ U JOIN CK :=
  ck_join U JOIN;
  [ let K := fresh "K" in let K2 := fresh "K2" in
    zstep; if_cases K; zify_cond K;
    try (ck_doneJ U JOIN);
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
            end);
    if_cases K2;
    first [ exfalso; unfold bv_lts in K2; rewrite ?land7_mod in K2;
            rewrite !signed_lit_small64 in K2 by (clear - CK; Z.div_mod_to_equations; lia);
            zify_bool K2; clear - CK K K2; Z.div_mod_to_equations; lia
          | ck_doneJ U JOIN ]
  | try clear CK ].
