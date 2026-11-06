(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec AgentLib SymExec2 SymExec2Sound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z37Corelib4Init5Logici22eq3h5LinuxProcessSemantics5Riscv5Instrjb7ALU_ADD3h5LinuxProcessSemantics5Riscv3Semm95alu6435stdpp9bitvectorbdefinitionsp37Z_to_bv37Corelib4Init9Datatypesra4boolra4truei23notjb5BC_NEm9cbranch_taken46Stdlib6ZArith6BinInt1Zvd6modulovd3powvd3subp32bvi23andvd2levd2ltvd4lxorvd3addp3bbv_unsignedra5falsejb7ALU_XORjb6BC_LTUjb7ALU_ANDjb6ALU_ORjb5BC_EQvd4landi22orjb6BC_GEU" s.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma bt_ne_add_lits : ltac2:(zQ "f0!h9!hf!j6!lf!ob!r0!t2!t9!u0!u6!ue!hh5!hhe!hi4!hia>1x@1$e@1$0#k0>2c1$1>2c2$1>0@1$8@3$2$1@2$b@2$d^2^1@2$c+2+k0Z@3$2$6@3$a$9@3$4$3^4@2$5@1$0#k0^3@3$4$3^4@2$5@1$0#k0^2$7").
Proof.
  intros x c1 c2 H. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Bool.negb_true_iff. apply Z.eqb_neq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (u64_range x) as Hx. intros E. apply H.
  rewrite Zplus_mod_idemp_r in E. rewrite Zplus_mod_idemp_r in E.
  replace (c1 - c2) with ((bv_unsigned x + c1) - (bv_unsigned x + c2)) by lia.
  rewrite Zminus_mod, E, <- Zminus_mod, Z.sub_diag. reflexivity.
Qed.

Lemma lxor_ones64 : ltac2:(zQ "80!hhe!hi4!hf!hif!j6!hj5!hja!hjf>1w$2>0@2$3@2$5Z^1@2$6^1@2$0+2+k0@3$4$2@2$7^2@2$1@2$0+2+k0+1@2$1@2$1@2$0+2+k0+1^2").
Proof.
  intros w Hw. change (2 ^ 64 - 1) with 18446744073709551615 at 1. rewrite lnot_mod64 by lia.
  unfold Z.lnot. rewrite <- Z.sub_1_r. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma bt_ltu_not_false : ltac2:(zQ "h10!h9!hk6!hj5!r0!hf!ob!hkc!t2!hla!j6!lf!hm2!hmc!ue!hhe!hi4!hia>1x@1$h0@1$0#k0>1c$4>1n$4>0@2$2Z@2$1@2$6@1$0#k0^3^2>0@2$2@2$1@2$1@2$6@1$0#k0^4^3^2@2$f@2$e+2+k0+1>0@2$2Z^3@3$9$7@3$d$c@3$5$b@3$5$a^6@2$3@1$0#k0^5@2$3@1$0#k0-1@2$3@1$0#k0^4$8").
Proof.
  intros x c n H1 H2 Hn. cbn [branch_taken alu64 alu]. unfold bv_ltu. apply Z.ltb_ge.
  rewrite bv_xor_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (u64_range x) as Hx.
  replace ((bv_unsigned x + c mod 2 ^ 64) mod 2 ^ 64) with (bv_unsigned x + c) by (rewrite Zplus_mod_idemp_r, Z.mod_small; lia).
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_ones64 by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bt_eq_and_or_lit_false : ltac2:(zQ "h30!h9!r0!hf!ob!j6!t2!hla!hif!u0!lf!hn5!hnf!ho8!ue!hp0!hj5!hja!hhe!hia>1x@1$h2@1$0#k0>1k$2>1c$2>0@2$7@2$fZ^2@2$h0^2@2$h1+2+k0>0@1$8@3$4$2@2$e^3+fZ@3$4$5@3$d$c@3$3$a@3$3$b@2$1@1$0#k0^4@3$3$9^5@2$1@1$0#k0^3@2$1@1$0#k0+f@2$1@1$0#k0Z$6").
Proof.
  intros x k c Hk Hk15. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_neq.
  rewrite bv_and_unsigned, bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (15 mod 2 ^ 64) with 15. change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small k) by lia.
  set (u := bv_unsigned (x + Z_to_bv 64 c)%bv). clearbody u.
  rewrite Z.land_lor_distr_l. intros E.
  apply Z.lor_eq_0_iff in E. destruct E as [E _]. exact (Hk15 E).
Qed.

(* [comment removed for export] *)
Lemma land_add_mask : ltac2:(zQ "70!hf!j6!hh5!hp7!hk6!hp0!hhe>1u$0>1c$0>1m$0>0@3$1$0@2$2^3+h0Z>0@2$3@3$1$0^2+3@2$3@3$1$0^2+7@3$1$0^2+f@3$1$0@2$5@2$2@2$4^5^4@2$6+2+k0^3@2$2^4@2$4^3+1").
Proof.
  intros u c m Hu Hm.
  assert (E : exists k, 2 <= k <= 4 /\ m = Z.ones k /\ m + 1 = 2 ^ k).
  { destruct Hm as [->|[->| ->]]; [exists 2 | exists 3 | exists 4]; (split; [lia|split; reflexivity]). }
  ndestruct E as (k & Hk & -> & Ek). rewrite Z.land_ones by lia. rewrite Ek.
  assert (D : exists q, 16 = 2 ^ k * q /\ 0 < q).
  { exists (2 ^ (4 - k)). split; [|apply Z.pow_pos_nonneg; lia].
    rewrite <- Z.pow_add_r by lia. replace (k + (4 - k)) with 4 by lia. reflexivity. }
  ndestruct D as (q & Hq & Hq0).
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (D64 : exists r, 2 ^ 64 = 2 ^ k * r).
  { exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. reflexivity. }
  destruct D64 as (r & Hr).
  set (v := (u + c) mod 2 ^ 64).
  assert (Hv : exists a, v = u + c - 2 ^ 64 * a) by (exists ((u + c) / 2 ^ 64); subst v; Z.div_mod_to_equations; lia).
  destruct Hv as (a & ->).
  assert (Hu' : exists b, u = 16 * b) by (exists (u / 16); Z.div_mod_to_equations; lia).
  destruct Hu' as (b & ->).
  replace (16 * b + c - 2 ^ 64 * a) with (c + (b * q - r * a) * 2 ^ k) by (rewrite Hr; nia).
  apply Z_mod_plus_full.
Qed.

Lemma bt_eq_and_add_lit_false : ltac2:(zQ "h10!hf!j6!h9!r0!hp7!ob!hh5!t2!hla!u0!lf!hn5!ho8!ue!hk6!hia!hkc>1x@1$f@1$2#k0>1c$0>1m$0>0@3$1$0@2$6@2$h0@1$2#k0^3+h0Z>0@2$4@3$1$0^2+3@2$4@3$1$0^2+7@3$1$0^2+f>0@1$9@3$1$0@2$6^4@2$e^3+1Z@3$1$7@3$d$c@3$5$b@3$5$a^6@2$3@1$2#k0^5@2$3@1$2#k0^4@2$3@1$2#k0Z$8").
Proof.
  intros x c m Hx Hm Hc. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_neq.
  rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small m) by lia. rewrite Zplus_mod_idemp_r.
  rewrite land_add_mask by assumption. exact Hc.
Qed.

Lemma bt_ne_and_add_lit_true : ltac2:(zQ "h10!hf!j6!h9!r0!hp7!ob!hh5!t2!t9!u0!lf!hn5!u6!ue!hk6!hia!hkc>1x@1$f@1$2#k0>1c$0>1m$0>0@3$1$0@2$6@2$h0@1$2#k0^3+h0Z>0@2$4@3$1$0^2+3@2$4@3$1$0^2+7@3$1$0^2+f>0@1$9@3$1$0@2$6^4@2$e^3+1Z@3$1$7@3$d$c@3$5$b@3$5$a^6@2$3@1$2#k0^5@2$3@1$2#k0^4@2$3@1$2#k0Z$8").
Proof.
  intros x c m Hx Hm Hc. pose proof (bt_eq_and_add_lit_false x c m Hx Hm Hc) as E. cbn [branch_taken] in E |- *.
  rewrite E. reflexivity.
Qed.

Lemma bt_eq_and_add_lit_true : ltac2:(zQ "h00!hf!j6!h9!r0!hp7!ob!hh5!t2!t9!lf!hn5!ho8!ue!hk6!hia!hkc>1x@1$e@1$2#k0>1c$0>1m$0>0@3$1$0@2$6@2$f@1$2#k0^3+h0Z>0@2$4@3$1$0^2+3@2$4@3$1$0^2+7@3$1$0^2+f>0@3$1$0@2$6^4@2$d^3+1Z@3$1$7@3$c$b@3$5$a@3$5$9^6@2$3@1$2#k0^5@2$3@1$2#k0^4@2$3@1$2#k0Z$8").
Proof.
  intros x c m Hx Hm Hc. cbn [branch_taken alu64 alu]. unfold bv_eqb. apply Z.eqb_eq.
  rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (0 mod 2 ^ 64) with 0. rewrite (Z.mod_small m) by lia. rewrite Zplus_mod_idemp_r.
  rewrite land_add_mask by assumption. exact Hc.
Qed.

Lemma bt_ne_and_add_lit_false : ltac2:(zQ "h00!hf!j6!h9!r0!hp7!ob!hh5!t2!hla!lf!hn5!u6!ue!hk6!hia!hkc>1x@1$e@1$2#k0>1c$0>1m$0>0@3$1$0@2$6@2$f@1$2#k0^3+h0Z>0@2$4@3$1$0^2+3@2$4@3$1$0^2+7@3$1$0^2+f>0@3$1$0@2$6^4@2$d^3+1Z@3$1$7@3$c$b@3$5$a@3$5$9^6@2$3@1$2#k0^5@2$3@1$2#k0^4@2$3@1$2#k0Z$8").
Proof.
  intros x c m Hx Hm Hc. pose proof (bt_eq_and_add_lit_true x c m Hx Hm Hc) as E. cbn [branch_taken] in E |- *.
  rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_add_lit : ltac2:(zQ "d0!h9!hkc!hk6!hf!hif!j6!lf!ob!hj5!hja!hhe!r0!hia>1x@1$c@1$0#k0>1c$3>0@2$4@2$8Z@2$2@2$1@1$0#k0^2^1@2$9@2$2@2$1@1$0#k0^2^1@2$a+2+k0@3$5$3@2$1@1$0#k0@3$7$6^3@2$b@1$0#k0^2@2$2@2$1@1$0#k0^3^2").
Proof.
  intros x c H. cbn [alu64 alu]. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma bt_ltu_add_lits : ltac2:(zQ "h00!h9!t2!hk6!hkc!hj5!hja!hif!hf!lf!ob!hhe!r0!j6!hmc!ue!hia>1x@1$f@1$0#k0>2c1$7>2c2$7>1b$1>0@2$6@2$4Z@2$2@2$3@1$0#k0^4^3@2$5@2$2@2$3@1$0#k0^4^3@2$a+2+k0>0@2$6@2$4Z@2$2@2$3@1$0#k0^5^3@2$5@2$2@2$3@1$0#k0^5^3@2$a+2+k0>0M1\1b$1P^3@2$5^5^4@2$4^4^5@3$c$1@3$e$d@3$9$8^7@2$b@1$0#k0^6@3$9$8^7@2$b@1$0#k0^5^4").
Proof.
  intros x c1 c2 b H1 H2 Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u_add_lit by assumption.
  destruct b; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma bt_geu_add_lits : ltac2:(zQ "h00!h9!t2!hk6!hkc!hj5!hja!hif!hf!lf!ob!hhe!r0!j6!hpc!ue!hia>1x@1$f@1$0#k0>2c1$7>2c2$7>1b$1>0@2$6@2$4Z@2$2@2$3@1$0#k0^4^3@2$5@2$2@2$3@1$0#k0^4^3@2$a+2+k0>0@2$6@2$4Z@2$2@2$3@1$0#k0^5^3@2$5@2$2@2$3@1$0#k0^5^3@2$a+2+k0>0M1\1b$1P^3@2$4^4^5@2$5^5^4@3$c$1@3$e$d@3$9$8^7@2$b@1$0#k0^6@3$9$8^7@2$b@1$0#k0^5^4").
Proof.
  intros x c1 c2 b H1 H2 Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u_add_lit by assumption.
  destruct b; cbn [negb]; [rewrite (proj2 (Z.ltb_ge _ _)) by lia | rewrite (proj2 (Z.ltb_lt _ _)) by lia]; reflexivity.
Qed.

Lemma bt_eq_add_lits_false : ltac2:(zQ "f0!h9!hf!j6!lf!ob!r0!t2!hla!u0!ho8!ue!hh5!hhe!hi4!hia>1x@1$e@1$0#k0>2c1$1>2c2$1>0@1$8@3$2$1@2$b@2$d^2^1@2$c+2+k0Z@3$2$6@3$a$9@3$4$3^4@2$5@1$0#k0^3@3$4$3^4@2$5@1$0#k0^2$7").
Proof.
  intros x c1 c2 H. pose proof (bt_ne_add_lits x c1 c2 H) as E. cbn [branch_taken] in E |- *.
  destruct (bv_eqb _ _); [discriminate|reflexivity].
Qed.
End FPX1.

(* [comment removed for export] *)
Ltac asc_br :=
  first
    [ apply bt_ne_add_lits; vm_compute; discriminate
    | apply bt_eq_add_lits_false; vm_compute; discriminate
    | apply bt_ltu_not_false; lia
    | apply bt_eq_and_or_lit_false; [lia | vm_compute; discriminate]
    | apply bt_eq_and_add_lit_false; [assumption | lia | vm_compute; discriminate]
    | apply bt_ne_and_add_lit_true; [assumption | lia | vm_compute; discriminate]
    | apply bt_eq_and_add_lit_true; [assumption | lia | reflexivity]
    | apply bt_ne_and_add_lit_false; [assumption | lia | reflexivity]
    | apply bt_ltu_add_lits; cbv iota; lia
    | apply bt_geu_add_lits; cbv iota; lia ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
