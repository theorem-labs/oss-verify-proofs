(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnWU Require Export BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma mod8_wrap : forall e, (e mod 8 = 0)%Z -> (bv_unsigned (Z_to_bv 64 e) mod 8 = 0)%Z.
Proof.
  intros e H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.
Lemma mod8_lor : forall x y, (x mod 8 = 0)%Z -> (y mod 8 = 0)%Z -> (Z.lor x y mod 8 = 0)%Z.
Proof.
  intros x y Hx Hy. change 8%Z with (2 ^ 3)%Z. rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
  change (2 ^ 3)%Z with 8%Z. rewrite Hx, Hy. reflexivity.
Qed.
Ltac ub_al_tac :=
  first [ assumption
        | (apply mod8_wrap; ub_al_tac)
        | (apply mod8_lor; ub_al_tac)
        | (Z.div_mod_to_equations; lia) ].
Lemma ub_land3 : forall x, (x mod 4 = 0)%Z -> Z.land x 3 = 0%Z.
Proof. intros x H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma ub_land3_wrap : forall e, (e mod 4 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 e)) 3 = 0%Z.
Proof.
  intros e H. apply ub_land3. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.
Ltac ub_land7 C :=
  repeat match type of C with
  | context [Z.land (bv_unsigned (Z_to_bv 64 ?e)) 7] => rewrite (land7_wrap e) in C by ub_al_tac
  | context [Z.land ?e 7] => rewrite (land7 e) in C by ub_al_tac
  | context [Z.land (bv_unsigned (Z_to_bv 64 ?e)) 3] => rewrite (ub_land3_wrap e) in C by (Z.div_mod_to_equations; lia)
  | context [Z.land ?e 3] => rewrite (ub_land3 e) in C by (Z.div_mod_to_equations; lia)
  end.

Ltac ub_unfold := idtac.
Ltac ub_pos_tac := first [ lia | (ub_unfold; lia) ].
Ltac ub_ltb C :=
  repeat match type of C with
  | context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) in C by ub_pos_tac | rewrite (proj2 (Z.ltb_ge x y)) in C by ub_pos_tac ]
  end.

Ltac ub_solve C :=
  first [ solve [clear - C; lia]
        | solve [ub_land7 C; clear - C; lia]
        | solve [ub_land7 C; lia]
        | solve [lia]
        | solve [ub_ltb C; cbn in C; first [ discriminate C | lia ]]
        | solve [rewrite ?Z.add_opp_r in C; first [ congruence | lia ]]
        | solve [ub_unfold; lia] ].

Ltac ub_sw :=
  repeat match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with context [bv_swrap 32 ?e] => rewrite (bn_swrap32_small e) by ub_pos_tac end
  end.
Ltac ub_lts :=
  repeat match goal with
  | |- context [bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      rewrite (lts_signed x y) by ub_pos_tac;
      first [ rewrite (proj2 (Z.ltb_lt x y)) by ub_pos_tac | rewrite (proj2 (Z.ltb_ge x y)) by ub_pos_tac ];
      cbv iota beta delta [negb]
  end.

Lemma ub_lxor_sign63 : forall x, (0 <= x < 9223372036854775808)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
  intros x H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. change 9223372036854775808%Z with (2 ^ 63)%Z. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 k) as [<-|NE]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma ub_land64_small : forall x, (0 <= x < 18446744073709551616)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

Ltac ub_wz C :=
  repeat match type of C with
         | context [bv_unsigned ?w] =>
             match w with
             | Z_to_bv _ _ => fail
             | _ => let w' := eval red in w in progress change w with w' in C
             end
         end.
Ltac ub_norm C :=
  ub_wz C; repeat (rewrite unsigned_lit in C by ub_pos_tac); repeat (rewrite ub_lxor_sign63 in C by ub_pos_tac);
  repeat (rewrite ub_land64_small in C by ub_pos_tac); ub_land7 C.

Ltac ub_ltb_cases C :=
  repeat match type of C with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end;
  cbn in C; first [ discriminate C | lia | (ub_unfold; lia) ].

Ltac ub_pc_lit := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => is_Zlit pc end.
Ltac ub_chk := zstep; ub_sw; ub_lts; first [ ub_pc_lit | if_false | let C := fresh "Cub" in if_cases C; [ exfalso; zify_cond C; ub_norm C; first [ ub_solve C | ub_ltb_cases C ] | clear C ] ].

Ltac ub1 kind :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ ub_chk | fail 100 "ub: cannot refute the UBSan trap condition at pc" pc ]
      end
  end.
