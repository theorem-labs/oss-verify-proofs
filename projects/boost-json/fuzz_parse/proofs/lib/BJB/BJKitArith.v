(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc6shiftr37Corelib4Init5Logicjd3andjd2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJKitArith~~~~~~lc6K24INVhc3divhc2lehc2lthc3mulhc3powlc9gcap_from37Corelib4Init9Datatypesse3natjd2orhc6of_natlc5agcap04Nposhc6shiftlhc3addhc3opp35stdpp9bitvectorbdefinitionshhd7Z_to_bvhhdbbv_unsignedse4boolhc3eqblc4xlen79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hm87v_sltiuhc4landjd2ex" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition K24INV : Z := 12297829382473034411.   (* [comment removed for export] *)

Lemma div24_mulhu : ltac2:(zQ "a0!h9!j4!l1!l7!pd!q6!qc!r1!r6!rc>1x$0>0@2$2@2$6Z^1@2$7^1@2$9+2+k0@3$3$0@2$1@2$1@2$8^2$4+k0+4@2$5^2+h8").
Proof.
  intros x Hx. unfold K24INV. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2^64 * 2^4) with (2^68).
  pose proof (Z.div_mod x 24 ltac:(lia)) as HE. pose proof (Z.mod_pos_bound x 24 ltac:(lia)) as R.
  set (q := x / 24) in *. set (r := x mod 24) in *.
  replace (x * 12297829382473034411) with (q * 2^68 + (8 * q + r * 12297829382473034411)) by (rewrite HE; lia).
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (8 * q + r * 12297829382473034411)); [lia|].
  assert (q < 2^60) by (subst q; apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma sdiv8_24 : ltac2:(zQ "60!h9!r6!l7!q6!qc!rc>3cur$0>0@2$4Z^1@3$2$0@2$3@2$1+h8^2@2$5+2+3@2$1+3^2").
Proof. intros cur Hc. change (2^3) with 8. rewrite <- (Z.div_mul (3*cur) 8) by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Fixpoint gcap_from (fuel : nat) (c need : Z) : Z :=
  match fuel with O => c | S f => if c <? need then gcap_from f (2 * c) need else c end.
Definition agcap : ltac2:(zQ "10!h9>4need$0$0") := ltac2:(zQ "20!h9!s2\4need$0@3$1Ni4+h0^1").

Lemma gcap_from_ge : ltac2:(zQ "b0!h9!s2!qc!r1!r6!u6!l1!l7!uc!v1!rc>4fuel$5>1c$0>4need$0>0@2$3Z^2>0@2$2^2@2$4^3@2$a+2@1$9^4@2$6@2$2^3@3$1^5^4^3@2$8@3$7$0@3$1^5^4^3^4@2$3@3$1^5^4^3@2$4+2^3").
Proof.
  induction fuel as [|fuel IH]; intros c need Hc Hn; cbn [gcap_from].
  - cbn in Hn. lia.
  - destruct (Z.ltb_spec c need).
    + destruct (IH (2*c) need ltac:(lia)) as [A B].
      { rewrite Nat2Z.inj_succ in Hn. rewrite Z.pow_succ_r in Hn by lia. lia. }
      split; [exact A|]. right. destruct B; lia.
    + lia.
Qed.

Lemma gcap_from_lower : ltac2:(zQ "40!h9!qc!u6!s2>4fuel$2>1c$0>4need$0>0@2$1Z^2@2$1^3@3$3^4^3^2").
Proof.
  induction fuel as [|fuel IH]; intros c need Hc; cbn [gcap_from]; [lia|].
  destruct (c <? need); [|lia]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma agcap_bounds : ltac2:(zQ "90!va!qc!l1!h9!l7!uc!r1!r6!rc>4need$3>0@2$2@2$1Z^1@2$1^1@2$8+2+i8@2$2@2$1^2@1$0^2@2$2@2$1+h0@1$0^2@2$5@3$4$3@1$0^2+h0@2$6@1$0^2@2$7+2^2").
Proof.
  intros need Hn. unfold agcap.
  destruct (gcap_from_ge 36 16 need ltac:(lia) ltac:(cbn; lia)) as [A B].
  pose proof (gcap_from_lower 36 16 need ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma bytes24 : ltac2:(zQ "d0!hg2!h9!hg8!l1!l7!hh1!qc!r1!r6!hh7!rc!hja!hk5>1g$1>0@2$3@2$6Z^1@2$7^1@2$a+2+i8@3$4$1@2$5@2$2^2+5@1$9@2$c@1$0#k0@2$b@1$0#k0@2$2^2+3@2$8+h8^2").
Proof. intros g Hg. rewrite !Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by (cbn; lia). cbn. lia. Qed.

(* [comment removed for export] *)
Definition xlen : ltac2:(zQ "10!h9>5chars$0$0") := ltac2:(zQ "40!hl4!h9!hh1!hlb\5chars$1M0\0$0$1@2$3^1ZZ@2$2^1+h8").

Lemma xlen_calc : ltac2:(zQ "d0!hg2!hja!hk5!h9!hh1!l1!l7!hm1!hq7!hr2!qc!r1!rc>5chars$3>0@2$5@2$aZ^1@2$b^1@2$c+2+je@3$6$3@2$9@2$2@1$0#k0@2$1@1$0#k0@2$4@2$2@1$0#k0@2$8@2$1@1$0#k0^2+1-1@2$2@1$0#k0@2$1@1$0#k0@2$4^2+h8@1$7^2").
Proof.
  intros chars Hc. rewrite v_sltiu_b2z. rewrite (unsigned_lit chars) by lia.
  change (bv_wrap 64 1) with 1. rewrite (unsigned_lit (chars + 24)) by lia. unfold xlen.
  destruct (Z.ltb_spec chars 1); destruct (Z.eqb_spec chars 0); try lia; cbn [Z.b2z].
  - rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit by lia. apply Z.land_0_l.
  - rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap. change ((0 + -1) mod 2^64) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma xlen_bounds : ltac2:(zQ "80!h9!hm1!l1!l7!qc!uc!hh1!r1>5chars$0>0@2$4Z^1@2$2@2$4Z@1$1^2@2$5@3$3$0@1$1^2Z@2$2@2$7Z^2@3$3$0@1$1^2@2$6^2+h8").
Proof. intros chars Hc. unfold xlen. destruct (Z.eqb_spec chars 0); lia. Qed.

(* [comment removed for export] *)
Lemma gcap_from_shape : ltac2:(zQ "90!h9!r1!l1!l7!s2!u6!hr9!uc!r6>4fuel$5>1c$0>4need$0>0@2$1Z^2@2$7@3$3$0@3$4^4^3^2^3@2$6$0\2c0$0@2$2@2$1Z^1@2$2@2$1^1^3@3$3$0@3$4^5^4^3@2$8+2^1").
Proof.
  induction fuel as [|fuel IH]; intros c need Hc; cbn [gcap_from]; [left; reflexivity|].
  destruct (Z.ltb_spec c need) as [LT|GE]; [| left; reflexivity]. right.
  destruct (IH (2 * c) need ltac:(lia)) as [E|(c0 & P0 & P1 & E)].
  - exists c. rewrite E. split; [exact Hc|]. split; [exact LT| reflexivity].
  - exists c0. split; [exact P0|]. split; [exact P1| exact E].
Qed.

(* [comment removed for export] *)
Lemma gcap_from_le_pow : ltac2:(zQ "90!rc!h9!u6!qc!l7!s2!r1!r6!v1>4fuel$2>1c$1>4need$1>1k$2>0@2$6Z^3>0@3$4$1@2$0+2+ha@2$7^4@2$0+2@1$8^2>0@2$3^4@2$0+2+ha@2$3@3$5^7^6^5@2$0+2+ha").
Proof.
  induction fuel as [|fuel IH]; intros c need k Hc Hk Hn; cbn [gcap_from].
  - pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k)). nia.
  - destruct (Z.ltb_spec c need).
    + destruct k as [|k].
      { cbn in Hk. exfalso. lia. }
      apply (IH (2 * c) need k); [lia| rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia; lia| exact Hn].
    + assert (1 <= 2 ^ Z.of_nat k) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k)); lia). nia.
Qed.
Lemma agcap_le_2p26 : ltac2:(zQ "40!qc!rc!h9!va>4need$2>0@2$0^1@2$1+2+ha@2$0@1$3^2@2$1+2+ha").
Proof. intros need Hn. unfold agcap. apply (gcap_from_le_pow 36 16 need 22%nat); [lia| reflexivity| exact Hn]. Qed.
(* [comment removed for export] *)
