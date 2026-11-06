(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec AgentLib.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf7Z_to_bv01Z37Corelib4Init5Logick92eq3h5LinuxProcessSemantics5Riscv5Instrm27ALU_ADD3h5LinuxProcessSemantics5Riscv3Semp05alu6446Stdlib6ZArith6BinInt1Zra3addhf2bvm27ALU_ANDra2lera6modulo37Corelib4Init9Datatypesv54boolk93andm25BC_EQp0cbranch_takenra3eqbra2ltra3powv54negbm25BC_NEk95Falsem2bbranch_condv54listv54consv56optionv54Somev53nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hob3rdnhfbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehtb7Segmentm25M_MULp07mul_divra3subv54truem26BC_GEUv55falsek92or" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma alu_add_Z : ltac2:(zQ "80!h9!jc!k6!ld!o6!r2!t2!t8>1a$2>1b$2@3$3@1$7@1$0#k0@3$5$4@2$1@1$0#k0^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6^2^1").
Proof.
  intros a b. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 a + Z_to_bv 64 b)%bv.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma alu_and3_Z : ltac2:(zQ "90!h9!jc!ld!k6!td!r2!u7!uc!t8>1a$3>0@2$6Z^1@3$2@1$8@1$0#k0@3$5$4@2$1@1$0#k0^2@2$1@1$0#k0+3@2$1@1$0#k0@2$7^2+4").
Proof.
  intros a Ha. apply bv_eq.
  change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 3)).
  rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2 ^ 2) with 4.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
Qed.
End FPX1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma bt_eq0_Z : ltac2:(zQ "c0!h9!jc!hgd!hh4!ld!k6!hha!hi2!hj1!u7!hj7!hjc>1a$5>0@2$3@2$9Z^1@2$a^1@2$b+2+k0@3$4$2@3$7$6@2$1@1$0#k0^2@2$1@1$0#k0Z@2$8^2Z").
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma bt_ne0_Z : ltac2:(zQ "d0!h9!jc!hgd!hk2!hh4!ld!k6!hk9!hi2!hj1!u7!hj7!hjc>1a$6>0@2$4@2$aZ^1@2$b^1@2$c+2+k0@3$5$2@3$8$7@2$1@1$0#k0^2@2$1@1$0#k0Z@1$3@2$9^2Z").
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bt_and3 : ltac2:(zQ "h00!hgd!hl1!h9!jc!ld!hl9!t2!k6!r2!hj1!uc!hk2!o6!td!hi2!u7>1c$5>1w$7>1k$7>1t$0>0@2$fZ@2$6^3^2>0M5\1c$5P^5@3$4$0@2$9@2$a@2$6^4^3+4Z^2@3$4$0@1$b@2$9@2$a@2$6^4^3+4Z^2$1$1$1$1@3$4$0@3$e^6@3$8$d@3$8$c@2$3@1$2#k0^5@2$3@1$2#k0^4@2$3@1$2#k0+3@2$3@1$2#k0Z^3").
Proof.
  intros c w k t Hw Hc. rewrite alu_add_Z, alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound (w + k) 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.

Lemma bt_and3_0 : ltac2:(zQ "e0!hgd!hl1!ld!h9!hl9!jc!hj1!uc!hk2!k6!td!r2!hi2!u7>1c$4>1w$9>1t$0>0@2$dZ^2>0M4\1c$4P^4@3$2$0@2$6@2$7^3+4Z^2@3$2$0@1$8@2$6@2$7^3+4Z^2$1$1$1$1@3$2$0@3$c^5@3$b$a@2$5@1$3#k0^4@2$5@1$3#k0+3@2$5@1$3#k0Z^3").
Proof.
  intros c w t Hw Hc. rewrite alu_and3_Z by lia.
  pose proof (Z.mod_pos_bound w 4 ltac:(lia)).
  destruct c; try contradiction.
  - rewrite bt_eq0_Z by lia. exact Hc.
  - rewrite bt_ne0_Z by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rdn_2 : ltac2:(zQ "f2!h9!t8!hm7!hme!hn5!hne!ho5!ld!hs6!t2!hsd!ih0!u7!hjc!jc&@3$3@1$1@1$0#8^3@1$6@1$1@1$0#8&@2$5@1$2@1$1@1$0#8~0>4segs@1$2$b>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>2b0@1$1@1$0#8>2b1@1$1@1$0#8>0@2$c@2$9@2$a@1$0#k0^3+2@2$d+2+k0>0@3$7@1$4@1$2@1$1@1$0#8@4$8^6^5^4N1~1>0@3$7@1$4@1$2@1$1@1$0#8@4$8^7^6@2$e@1$0#k0@2$9@2$a@1$0#k0^5+1N1~1@3$7@1$4@1$2@1$1@1$0#8@4$8^8^7^6N2@2$5@1$2@1$1@1$0#8@3$3@1$1@1$0#8^5@3$3@1$1@1$0#8^4@1$6@1$1@1$0#8").
Proof.
  intros segs m a b0 b1 Hnw H0 H1. cbn [rdn] in *.
  destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x|]; [|discriminate].
  injection H0 as ->.
  replace (a + 1)%bv with (Z_to_bv 64 (bv_unsigned a + 1)).
  2:{ apply bv_eq. rewrite u64_lit by (pose proof (u64_range a); lia). symmetry. apply u_add1. lia. }
  destruct (match m (Z_to_bv 64 (bv_unsigned a + 1)) with Some b => Some b | None => seg_rom segs _ end) as [y|];
    [|discriminate].
  injection H1 as ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lin_neg1_val : ltac2:(zQ "b0!h9!jc!t8!ld!k6!o6!ihb!r2!ii3!iid!hsd>1x@1$2@1$0#k0>1c$4@3$3@1$2@1$0#k0@3$7$5@4$8@1$0#k0$6@2$1@1$0#k0-1^2@2$1@1$0#k0^1@2$1@1$0#k0@2$9^1@2$a@1$0#k0^2").
Proof.
  intros x c. apply bv_eq.
  change (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c))
    with ((Z_to_bv 64 (-1) * x) + Z_to_bv 64 c)%bv.
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  rewrite <- Z.add_mod by lia.
  replace ((2 ^ 64 - 1) * bv_unsigned x + c) with ((c - bv_unsigned x) + bv_unsigned x * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma bt_geu_Z : ltac2:(zQ "c0!h9!k6!u7!jc!hgd!ij3!hh4!ld!ija!hi2!hj7!hjc>1a$1>1b$1>0@2$6@2$2Z^1@2$2^1^2>0@2$a^3@2$b+2+k0@3$7$4@3$9$8@2$3@1$0#k0^4@2$3@1$0#k0^3$5").
Proof.
  intros a b Hab Ha. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma bt_geu_Z_false : ltac2:(zQ "c0!h9!k6!hj7!jc!hgd!ik3!hh4!ld!ija!hi2!u7!hjc>1a$1>1b$1>0@2$6@2$aZ^2@2$2^2^1>0@2$2^2@2$b+2+k0@3$7$4@3$9$8@2$3@1$0#k0^4@2$3@1$0#k0^3$5").
Proof.
  intros a b Hab Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
  apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.

End FPX2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma mod4_shift : ltac2:(zQ "40!k6!uc!ld!t2>1w$0>1k$0>1r$0>0@3$2$0@2$1^3+4^1@3$2$0@2$1@2$3^4^3+4@2$1@2$3^2^3+4").
Proof. intros w k r H. rewrite <- Zplus_mod_idemp_l, H. reflexivity. Qed.

Lemma mod4_cases : ltac2:(zQ "40!k6!ld!uc!ikb>1w$0@2$3@3$1$0@2$2^1+4Z@2$3@3$1$0@2$2^1+4+1@2$3@3$1$0@2$2^1+4+2@3$1$0@2$2^1+4+3").
Proof. intros w. lia. Qed.
End FPX3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
