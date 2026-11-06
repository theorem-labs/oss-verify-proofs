(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec AgentLib SymExec2 SymExec2Sound MainDefs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3powhc6modulo04Nposhc3mulhc6shiftr35stdpp9bitvectorbdefinitionsl88bv_swrap37Corelib4Init9Datatypeso04bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MainArith4FPX1~~~~~~pf8cfg_hi_Zhc3eqbo03nato04true37Corelib4Init5Logicve2eq37Corelib5Lists7ListDefhh73maphh73seqpf9cfg_hi_ok36Stdlib5Lists4Listhk87forallbhc6of_natve3andhc2lehc2lthc3addhc3lorl87Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hp55v_mulhp54v_orhp55v_srll82bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~huf5hdr_bo04listhuf7hdr_cfg" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition cfg_hi_Z : ltac2:(zQ "10!h9>2b1$0$0") := ltac2:(zQ "70!j4!ja!k3!h9!k9!kf!n5\2b1$3@2$5@2$1@2$4@2$0+2+j9@2$1@2$6@1$2#8^1@2$0+2+k0@2$0+2+k0+j1").

Definition cfg_hi_ok : ltac2:(zQ "20!p8!h9>2b1$1$0") := ltac2:(zQ "50!h9!u0!ub!ja!k9\2b1$0@2$2@1$1^1@2$4+hg0@2$3^1+o0").

Lemma cfg_hi_all : ltac2:(zQ "a0!h9!p8!v1!v7!hh2!hie!hj5!hjc!hlb!hm6@3$4$1@3$8$0$7@4$5$2$0$9@2$6N0Nhg0$3").
Proof. vm_compute. reflexivity. Qed.

Lemma cfg_hi_val : ltac2:(zQ "80!h9!hmf!hh2!u0!hn5!hna!ja!k9>2b1$0>0@2$1@2$4Z^1@2$5^1+hg0@3$2$0@1$3^2@2$7+hg0@2$6^2+o0").
Proof.
  intros b1 Hb.
  assert (Hin : In b1 (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b1). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) cfg_hi_all b1 Hin) as H. unfold cfg_hi_ok in H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma lor_disjoint_add : ltac2:(zQ "80!h9!hn5!k9!hmf!hh2!hnf!ho5!hna>1a$0>1k$0>0@2$3@2$1Z^2@2$7^2+hg0>0@2$1Z^2@3$4$0@2$6@2$2+hg0^3^4@2$5@2$2+hg0^3^4").
Proof.
  intros a k Ha Hk. rewrite <- Z.lxor_lor.
  - symmetry. rewrite Z.add_comm. rewrite Z.add_nocarry_lxor. + apply Z.lxor_comm. + 
      rewrite Z.land_comm.
      apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z_lt_le_dec n 8) as [Hl|Hh].
      * replace (256 * k) with (k * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits by lia.
        rewrite (Z.testbit_neg_r k) by lia. reflexivity.
      * rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia |].
        destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
        apply Z.lt_le_trans with (m := 8); [|lia]. apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [Hl|Hh].
    + replace (256 * k) with (k * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits by lia.
      rewrite (Z.testbit_neg_r k) by lia. reflexivity.
    + rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia |].
      destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
      apply Z.lt_le_trans with (m := 8); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma cfg_word : ltac2:(zQ "h00!k3!hob!hmf!h9!hn5!hna!hh2!ht0!ht9!hu1!hnf!ja!k9!j4!hua!n5>2b0$3>2b1$3>0@2$2@2$4Z^2@2$5^2+hg0>0@2$2@2$4Z^2@2$5^2+hg0@3$6@1$e@1$0#k0@2$8@2$9@2$7@2$1@1$0#k0@2$d+2+j9@2$1@1$0#k0@2$f@1$0#8^3@2$1@1$0#k0+j1@2$1@1$0#k0^4@2$1@1$0#k0@2$b@2$a^4@2$c+hg0^3+ogg0").
Proof.
  intros b0 b1 H0 H1.
  unfold v_or, v_srl, v_mul. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (49 mod 2 ^ 64 mod 64) with 49. rewrite (Z.mod_small (2 ^ 57)) by lia.
  pose proof (cfg_hi_val b1 H1) as Hv. unfold cfg_hi_Z in Hv.
  assert (Hr : 0 <= 256 * (b1 mod 128) < 2 ^ 64) by (pose proof (Z.mod_pos_bound b1 128); lia).
  rewrite (Z.mod_small (Z.shiftr _ 49)).
  2:{ rewrite Hv. exact Hr. }
  rewrite Hv. rewrite (Z.mod_small b0) by lia.
  rewrite lor_disjoint_add by (pose proof (Z.mod_pos_bound b1 128); lia).
  f_equal. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as Hm.
  replace (b0 + 256 * b1) with ((b0 + 256 * (b1 mod 128)) + (b1 / 128) * 32768)
    by (rewrite (Z.div_mod b1 128) at 1 by lia; lia).
  rewrite Z_mod_plus_full. symmetry. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hdr_b_range : ltac2:(zQ "80!iia!ij3!v1!hmf!k3!hn5!hna!hua>4data@1$1@1$7@1$4#8>1i$2@2$3@2$5Z@2$0^2^1@2$6@2$0^2^1+hg0").
Proof.
  intros data i. unfold hdr_b. pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as Hr.
  unfold bv_modulus in Hr. cbn in Hr. lia.
Qed.

Lemma hdr_cfg_range : ltac2:(zQ "70!ija!ij3!hmf!k3!hn5!hna!hua>4data@1$1@1$6@1$3#8@2$2@2$4Z@1$0^1@2$5@1$0^1+ogg0").
Proof. intros. unfold hdr_cfg. apply Z.mod_pos_bound. lia. Qed.
End FPX1.
(* [comment removed for export] *)
