(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MemSplit.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq3h5LinuxProcessSemantics5Riscv7Preludelabbvmap_empty69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~oe4getrhf7Z_to_bv01Z46Stdlib6ZArith6BinInt1Ztd3powtd2lek13andtd4landtd2lttd6modulotd3suboe6v_andihfbbv_unsignedtd4onesoe6v_subw37Corelib4Init9Datatypeshk83nat3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehm7dZ_to_le_byteshk84list37Corelib4Init5Peanohqf2le37Corelib5Lists7ListDefhs96firstn3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshuah0word_to_le_byteshk86optionhk84Someoe3rdn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeike7Segmenthm7dbytes_le_to_Zoe4v_lw" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma getr_empty : ltac2:(zQ "60!h9!jc!l5!o0!s9!t0>1r@1$1@1$0#5@3$2@1$1@1$0#k0@2$4@2$3@1$0#5@1$1@1$0#k0^1@2$5@1$0#k0Z").
Proof.
  intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
  unfold reg_get, bvmap_get, bvmap_empty.
  destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma land_align_mask : ltac2:(zQ "90!ta!v5!vb!hg0!l5!hg6!hgd!hh2!hhb>1a$0>1k$0>0@2$3@2$2Z^2@2$6^2@2$1+2+k0>0@2$3@2$2Z^2@2$2^2+k0>0@3$4$0@2$7^4@2$1+2^3Z@3$4$0@2$5^5@2$8@2$1+2+k0@2$1+2^4^5").
Proof.
  intros a k Ha Hk Hmod.
  replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m16_aligned : ltac2:(zQ "70!h9!l5!jc!ta!hi1!hh2!hia>1x@1$2@1$0#k0>0@3$1$3@2$5@2$6@1$0#k0^1+h0Z@3$1@1$2@1$0#k0@2$4^2-h0^2").
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-16)) with (2^64 - 2^4).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_low_zero : ltac2:(zQ "70!ta!l5!vb!hg6!hh2!hj8!v5>1a$0>1k$0>0@2$2Z^2>0@2$2Z^2>0@3$1$0@2$4^4@2$6+2^3Z@3$1$0@2$3^5@1$5^4Z").
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.

Lemma v_andi_3_aligned : ltac2:(zQ "80!h9!l5!jc!ta!hi1!hh2!t0!hia>1x@1$2@1$0#k0>0@3$1$3@2$5@2$7@1$0#k0^1+4Z@3$1@1$2@1$0#k0@2$4^2+3@2$6@1$0#k0Z").
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.

Lemma land_4_aligned8 : ltac2:(zQ "50!ta!l5!hg6!vb!hh2>1a$0>0@2$3Z^1>0@3$1$0@2$4^2+8Z@3$1$0@2$2^3+4Z").
Proof.
  intros a Ha Hm.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
  subst i.
  replace a with ((a / 8) * 2^3) by lia.
  rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
  rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma v_andi_4_aligned8 : ltac2:(zQ "80!h9!l5!jc!ta!hi1!hh2!t0!hia>1x@1$2@1$0#k0>0@3$1$3@2$5@2$7@1$0#k0^1+8Z@3$1@1$2@1$0#k0@2$4^2+4@2$6@1$0#k0Z").
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.

Lemma mod4_mod_pow2 : ltac2:(zQ "50!ta!hh2!l5!vb!v5>1t$0>1k$0>0@2$3+2^1@3$2$0@2$1@2$1^3@2$4+2^2+4@2$1^3+4").
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3_aligned : ltac2:(zQ "90!h9!l5!t0!jc!ta!hi1!hjf!hh2!hia>1x@1$3@1$0#k0>0@3$1$4@2$7@2$8@1$0#k0^1+4Z@3$1@1$3@1$0#k0@2$5@2$6@2$2@1$0#k0Z^2+3@2$2@1$0#k0Z").
Proof.
  intros x Hm. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31).
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
  rewrite mod4_mod_pow2 by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2 by lia.
  replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
  2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
      rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_Z_to_le_bytes : ltac2:(zQ "90!hm0!h9!hp6!jc!hq7!l5!hs3!hu0!ta>1k$0>1n$0>1z$8>0@2$6^3^2@3$5@1$4@1$3@1$1#8@3$7@1$3@1$1#8^4@2$2^3^2@2$2^4^2").
Proof.
  induction k as [|k IH]; intros n z Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_word_to_le_bytes : ltac2:(zQ "80!h9!jc!hm0!ii1!hq7!l5!hs3!hu0>1k$2>1n$2>1v@1$1@1$0#k0>0@2$6^3^2@3$5@1$4@1$1@1$0#8@3$7@1$1@1$0#8^4@2$3^3^2@2$3^4^2").
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.

(* [comment removed for export] *)
Lemma rdn_low_bytes : ltac2:(zQ "b0!h9!jc!hq7!ij6!ik0!l5!ii1!ik8!hm0!hs3!io3>4segs@1$2$a>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1v@1$1@1$0#k0>1k$8>0@2$9^1N8>0@3$5@1$3@1$2@1$1@1$0#8@4$7^6^5^4N8@2$4@1$2@1$1@1$0#8@2$6N8^3@3$5@1$3@1$2@1$1@1$0#8@4$7^7^6^5^3@2$4@1$2@1$1@1$0#8@2$6^3^4").
Proof.
  intros segs m a v k Hk H.
  rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.

Lemma bytes_le_to_Z_4_small : ltac2:(zQ "90!h9!hia!l5!ta!ioe!ii1!hgd!v5!jc>1v@1$8@1$0#k0>0@2$6@2$1@1$0#k0^1@2$7+2+i0@3$2$3@1$4@2$5N4^2@2$1@1$0#k0^2").
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : ltac2:(zQ "70!h9!jc!l5!ipf!hgd!v5!hia>1v@1$1@1$0#k0>0@2$4@2$6@1$0#k0^1@2$5+2+hf@3$2@1$1@1$0#k0@1$3^2^2").
Proof.
  intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (u64_range v).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_u_eq : ltac2:(zQ "60!h9!l5!ta!jc!t0!hia>1a@1$3@1$0#k0>1z$2>0@3$1$2^1@2$5@1$0#k0^2@3$1@1$3@1$0#k0@2$4@1$0#k0^2^3").
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_u_eq_sym : ltac2:(zQ "60!h9!l5!ta!jc!t0!hia>1a@1$3@1$0#k0>1z$2>0@3$1$2^1@2$5@1$0#k0^2@3$1@1$3@1$0#k0^3@2$4@1$0#k0^2").
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
End FPX2.
(* [comment removed for export] *)
