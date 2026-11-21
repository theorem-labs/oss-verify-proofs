(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Export ZStep ZMem ZPrune.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZTac ZCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac nc_concl f := lazymatch goal with |- ?g => let g' := f g in change_no_check g' end.
Ltac nc_change a c :=
  lazymatch goal with |- ?g =>
    lazymatch (eval pattern a in g) with
    | ?F _ => let g' := eval cbv beta in (F c) in change_no_check g'
    end end.

Ltac znorm_tree ::=
  nc_concl ltac:(fun g => eval cbv beta iota delta [wb zrd_l zget_l zalu zalu32 zalu32u zmul zmul32 zcond zjalr_tgt] in g);
  nc_concl ltac:(fun g => eval cbn beta iota delta [alookup Pos.eqb] in g);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd ?Rb _) _ _) _ =>
      tryif is_var Rb then idtac else nc_concl ltac:(fun g => eval cbv beta iota delta [zget tget] in g)
  | |- context [zget ?Rb _] => tryif is_var Rb then idtac else nc_concl ltac:(fun g => eval cbv beta iota delta [zget tget] in g)
  | |- _ => idtac
  end.

Ltac zfold_step ::=
  match goal with
  | |- context [?a + ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a + b) in nc_change (a + b) c
  | |- context [?a - ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a - b) in nc_change (a - b) c
  | |- context [?a * ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a * b) in nc_change (a * b) c
  | |- context [Z.shiftl ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.shiftl a b) in nc_change (Z.shiftl a b) c
  | |- context [Z.shiftr ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.shiftr a b) in nc_change (Z.shiftr a b) c
  | |- context [Z.land ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.land a b) in nc_change (Z.land a b) c
  | |- context [Z.lor ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.lor a b) in nc_change (Z.lor a b) c
  | |- context [?a mod ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a mod b) in nc_change (a mod b) c
  | |- context [bv_swrap ?n ?a] =>
      is_zlit a;
      let c := eval cbv in (bv_swrap n a) in nc_change (bv_swrap n a) c
  | |- context [page_round_up_Z ?a] =>
      is_zlit a;
      let c := eval cbv in (page_round_up_Z a) in nc_change (page_round_up_Z a) c
  | |- context [?x + ?a + ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a + b) in
      rewrite (zadd_assoc_fold x a b c eq_refl)
  | |- context [?x - ?a] =>
      is_zlit a;
      lazymatch a with Z0 => fail | _ => idtac end;
      let c := eval cbv in (- a) in
      rewrite (zsub_fold x a); nc_change (- a) c
  | |- context [?x + 0] => rewrite (zadd_0_r' x)
  | |- context [0 + ?x] => rewrite (zadd_0_l' x)
  end.

Ltac zc_x0 r ::= let v := eval cbv in (is_x0 r) in nc_change (is_x0 r) v.

Ltac zc_key r ::= let v := eval cbv in (bv_key r) in nc_change (bv_key r) v.

Ltac zc_s n i ::= let v := eval cbv in (@bv_signed n i) in nc_change (@bv_signed n i) v.

Ltac zc_u n i ::= let v := eval cbv in (@bv_unsigned n i) in nc_change (@bv_unsigned n i) v.

Ltac zrefold_getl ::=
  repeat match goal with
  | |- context [match alookup ?l ?k with Some e => e | None => zget ?Rb _ end] =>
      nc_change (match alookup l k with Some e => e | None => zget Rb k end) (zget_l Rb l k)
  end.

Ltac zbase ::=
  repeat match goal with
  | H : alookup ?l ?k = _ |- context [alookup ?l ?k] => rewrite H; nc_concl ltac:(fun g => eval cbv iota in g)
  end;
  zrefold_getl;
  repeat match goal with
  | H : zget_l ?Rb ?l ?k = _ |- context [zget_l ?Rb ?l ?k] => rewrite H
  | H : zget ?Rb ?k = _ |- context [zget ?Rb ?k] => rewrite H
  end.

Ltac zdedup ::=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
      lazymatch l with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
          tryif list_is_explicit l
          then (rewrite zcfg_dedup; nc_concl ltac:(fun g => eval cbv beta iota delta [dedup remove_key Pos.eqb] in g))
          else idtac
      | _ => idtac
      end
  | |- _ => idtac
  end.

Ltac znorm_pre ::= nc_concl ltac:(fun g => eval cbv beta delta [zrd_l wb] in g).

Ltac zwith_list_hidden tac ::=
  first
  [ let L := zgoal_list in
    zbig_list L;
    let k := fresh "zL" in
    set (k := L) in |- *; tac; nc_concl ltac:(fun g => eval cbv delta [k] in g); clear k
  | tac ].

Ltac zwith_tail_hidden tac ::=
  first
  [ let L := zgoal_list in
    lazymatch L with
    | _ :: ?tl =>
        zbig_list tl;
        let k := fresh "zL" in
        set (k := tl) in |- *; tac; nc_concl ltac:(fun g => eval cbv delta [k] in g); clear k
    end
  | tac ].

Ltac znorm_tree1 ::= nc_concl ltac:(fun g => eval cbv beta iota delta [wb zrd_l zget_l zalu zalu32 zalu32u zmul zmul32 zcond zjalr_tgt] in g).

Ltac znorm_tree2 ::=
  nc_concl ltac:(fun g => eval cbn beta iota delta [alookup Pos.eqb] in g);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd ?Rb _) _ _) _ =>
      tryif is_var Rb then idtac else nc_concl ltac:(fun g => eval cbv beta iota delta [zget tget] in g)
  | |- context [zget ?Rb _] => tryif is_var Rb then idtac else nc_concl ltac:(fun g => eval cbv beta iota delta [zget tget] in g)
  | |- _ => idtac
  end.

Ltac zlen_fold_closed ::=
  repeat match goal with
  | |- context [Z.of_nat (@length ?A ?x)] =>
      lazymatch x with context [Z.to_nat _] => fail | _ => idtac end;
      let n := eval lazy in (Z.of_nat (@length A x)) in
      is_zlit n; nc_change (Z.of_nat (@length A x)) n
  end.

Ltac zcbv_iota ::= nc_concl ltac:(fun g => eval cbv iota in g).

Ltac zcond_tac ::=
  nc_concl ltac:(fun g => eval cbv beta iota delta [zcond] in g);
  repeat match goal with H : ?x mod 18446744073709551616 = _ |- context [?x mod 18446744073709551616] => rewrite H end;
  rewrite ?mod_small_u64 by zlia;
  rewrite ?swrap64_small by zlia; rewrite ?swrap32_small by zlia;
  first [ reflexivity | zcond_decide ].
