(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Local Close Scope Z_scope.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Ltac nreg_val R n :=
  let p := eval vm_compute in (Z.to_pos (n + 1)) in
  let v := eval lazy beta iota delta [tget] in (tget p R) in
  lazymatch v with Some ?x => x end.
Ltac nforget n :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := nreg_val R n in
    tryif is_var x then idtac else
    (let y8 := nreg_val R 8%Z in let y18 := nreg_val R 18%Z in let y19 := nreg_val R 19%Z in let y20 := nreg_val R 20%Z in
     tryif first [constr_eq x y8 | constr_eq x y18 | constr_eq x y19 | constr_eq x y20] then idtac
     else (let j := fresh "jk" in generalize x; intro j))
  end.
Ltac nforget_F :=
  lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) =>
    tryif is_var F then idtac else (let j := fresh "jF" in generalize F; intro j) end.

Ltac nforget_all keep :=
  let go n := (tryif keep n then nforget n else idtac) in
  go 1%Z; go 5%Z; go 6%Z; go 7%Z; go 9%Z; go 10%Z; go 11%Z; go 12%Z; go 13%Z; go 14%Z; go 15%Z; go 16%Z; go 17%Z;
  go 21%Z; go 22%Z; go 23%Z; go 24%Z; go 25%Z; go 26%Z; go 27%Z; go 28%Z; go 29%Z; go 30%Z; go 31%Z;
  nforget_F.
Ltac srun_cut_f cuts keep :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc end; nstep; nforget_all keep).
Ltac nexp_f cuts fin keep := srun_cut_f cuts keep; first [ fin | (nbranch; nexp_f cuts fin keep) ].

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_tables.
Lemma sown_read_at : forall (m : word -> option byte) c a, mem_inv usegs m -> (0 <= c < 256)%Z -> a = wa (T_SOWN + c) ->
  ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (sown c)].
Proof. intros m c a MI Hc ->. apply sown_read; assumption. Qed.
Ltac s2_load_sown :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := lazymatch Ea with
                     | Z.add 83920%Z ?i => i
                     | Z.add ?i 83920%Z => i
                     end in
          rewrite (sown_read_at m idx a MIh ltac:(lia) ltac:(unfold wa, T_SOWN; f_equal; lia))
      end
  end;
  load_post.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjExpDigits.
Lemma dval_step_wz : forall bs q c, (0 <= c)%Z -> (48 <= B bs (q + c) <= 57)%Z ->
  Z_to_bv 64 (dval bs q c mod 18446744073709551616 * 10 + Z.land (B bs (q + c) + -48) 255) = Z_to_bv 64 (dval bs q (c + 1)).
Proof.
  intros bs q c Hc HB. apply wz_eq_mod. rewrite dval_S by lia.
  rewrite (land255_small (B bs (q + c) + -48)) by lia.
  rewrite Z.add_mod by lia. rewrite Z.mul_mod_idemp_l by lia. rewrite <- Z.add_mod by lia.
  reflexivity.
Qed.

Lemma V8_low : forall b1 b2 b3 b4 b5 b6 b7 b8,
  (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= b3 < 256)%Z -> (0 <= b4 < 256)%Z -> (0 <= b5 < 256)%Z -> (0 <= b6 < 256)%Z -> (0 <= b7 < 256)%Z -> (0 <= b8 < 256)%Z ->
  (V8 b1 b2 b3 b4 b5 b6 b7 b8 mod 256 = b1)%Z.
Proof. intros. rewrite V8_sum by lia. lia. Qed.
Lemma low_sub48 : forall x b, (x mod 256 = b)%Z -> ((x + -48) mod 256 = (b + -48) mod 256)%Z.
Proof. intros x b H. rewrite <- H. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.
Lemma low_lor32 : forall x, (0 <= x)%Z -> (Z.lor x 32 mod 256 = Z.lor (x mod 256) 32)%Z.
Proof.
  intros x Hx. change 256%Z with (2 ^ 8)%Z. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. reflexivity.
Qed.

Lemma low_e_nz : forall x b, (x mod 256 = b)%Z -> (Z.land (Z.lor x 32) 255 = 101)%Z -> (b <> 0)%Z.
Proof.
  intros x b H K E0. subst b. rewrite Z.land_lor_distr_l in K. change (Z.land 32 255) with 32%Z in K.
  change 255%Z with (Z.ones 8) in K. rewrite Z.land_ones in K by lia. change (2 ^ 8)%Z with 256%Z in K. rewrite E0 in K. discriminate K.
Qed.

Ltac ngstep := first [ gguard | nstep ].
Ltac ngrun := repeat ngstep.
Ltac ngrun_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          ngstep).

Ltac ngrun_cut cuts :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc
          | _ => idtac end;
          ngstep).
Ltac ngbranch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      first [ n_closed_branch a b | (let KB := fresh "KB" in if_cases KB) ]
  end.
Ltac ngexp cuts fin := ngrun_cut cuts; first [ fin | (ngbranch; ngexp cuts fin) ].
Ltac ngrun_cut_f cuts keep :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc
          | _ => idtac end;
          ngstep; nforget_all keep).
Ltac ngexp_f cuts fin keep := ngrun_cut_f cuts keep; first [ fin | (ngbranch; ngexp_f cuts fin keep) ].
