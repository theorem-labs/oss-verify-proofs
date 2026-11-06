(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_B MallocModel_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jb5usage37Corelib4Init5Logico12eqjb6mstatejb9set_usage46Stdlib6ZArith6BinInt1Zqf3eqb04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~t36usages35stdpp9bitvectorbdefinitionshhe2bvhc4listo13andt32wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hl33updqf2leqf2ltqf6to_nat25stdpp9countablehq7bZ_countable35stdpp7numbers1Zhs76eq_decjb9unmap_seq25stdpp4gmaphue4gmapjbbc_unmap_seqjb4mctxjbh1set_unmap_seq_mapjb7upd_ctx25stdpp4baseij66insert25stdpp8fin_mapsikcamap_inserthueh2gmap_partial_altert3aunmap_seqst32b8jb5c_seqjb3ctxjb7set_seqjb8step_seqqf3addij65emptyhueagmap_emptyjbarecord_seqjbfsc_in_seq_rangeqf3subjbcget_meta_recjb4aptrjb4metajb4concjb5oconcjb4optrjbaset_activet39meta_slotjbam_freeablejbam_last_idxjb8m_maplenjbbm_sizeclassqf3powt39meta_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocKit_B3~~~~~~jo95mw_okqf4landqf3mulqf6shiftro13iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~jv33sxvqf3opphhe7Z_to_bvhhe8bv_swraphhebbv_unsignedqf5ldiff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kn43le4hc4conshc3nilkn43le1qf6moduloqf6shiftlqf3lor" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma usage_set_usage : ltac2:(zQ "70!h9!j4!n9!p5!pa!q3!s7>2st$4>2sc$0>1v$0>1i$0@3$3$0@2$2@3$5^3^2^4^1M1\0$1$0@2$6^1^3^2@2$2^4^1").
Proof. intros st sc v i.
  unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
  destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma usages_set_usage : ltac2:(zQ "e0!sd!h9!hh5!hjb!hk1!hk8!p5!hke!hod!pa!q3!hp4!hp9!hpe>2st$9>2sc$1>1v$1>0@2$5@2$bZ^2@2$c^2+j0@3$6@1$4@1$3@1$0#k0@1$2@3$a^3^2^4@4$8@1$3@1$0#k0@1$2^4@1$d^3@1$7^2").
Proof. intros st sc v.
  intros Hsc. unfold usages.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite usage_set_usage.
  destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

Lemma unmap_seq_set : ltac2:(zQ "h00!h9!hr8!ht8!j4!hu2!hva!p5!ig2!ih0!pa!ih7!iic!s7!ik2!ilc!ima>2st$9>1i$0>1v$0>1j$0@3$6$0@2$4@2$b\1c$8@2$a@7$d$0$0@4$5$0$2$1$0@4$e$0$0@4$5$0$2$1$0@4$f$0$2$1$0^4^3@1$7^1^1^4^1M3\0$3$0@2$c^1^3^2@2$4^4^1").
Proof. intros st i v j.
  unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma unmap_seqs_set : ltac2:(zQ "h70!h9!hr8!ht8!sd!io1!hjb!hva!hk1!hk8!p5!ioe!hod!ig2!ih0!pa!ih7!iic!hp4!hp9!hpe!ik2!ilc!ima>2st$e>1i$0>1v$0>0@2$8@2$h1Z^2@2$h2^2+i0@3$9@1$7@1$5@1$3#8@1$4@2$h0\1c$d@2$f@7$h4$0$0@4$6$0$2$1$0@4$h5$0$0@4$6$0$2$1$0@4$h6$0$2$1$0^4^3@1$c^1^1^4@4$b@1$5@1$3#8@1$4^4@1$h3^3@1$a^2").
Proof. intros st i v.
  intros Hi. unfold unmap_seqs.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite unmap_seq_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma step_seq_eq : ltac2:(zQ "h20!h9!pa!iic!j4!ip3!ipb!iq1!hr8!ht8!p5!ih0!ih7!iqb!ir6!s7!irc!hva!is5>2st$1@3$9$1@1$c^1M3\0$3$1@2$e@1$4@1$5^1+vf@2$2@1$6+1@2$2\1c$a@2$b@2$f@4$h0$0$8$7$0@4$h1$0$8$7$0^1^1@2$2@1$6@2$d@1$4@1$5^1+1^1").
Proof. intros st. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq : ltac2:(zQ "h20!h9!pa!hr8!ht8!j4!hva!p5!ip3!ig2!ih0!it3!iu0!ih7!iic!iv2!ik2!ilc!ima>2sc$0>2st$1@3$6$1@2$a^2^1M4\0$4$1@1$b^2@2$d\1c$9@2$c@7$f$0$0@4$5$0$3$2$0@4$h0$0$0@4$5$0$3$2$0@4$h1$0$3$2$0@2$e^3+7@1$7^1@1$8^1^1^1^1").
Proof. intros sc st. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rec_upd_ctx : ltac2:(zQ "70!iv8!ih0!p5!jg7!jge!pa!iic>2st$5>1f>0$1$1>1q$3@3$2$4@2$0@2$6^2^3^1@2$0^3^1"). Proof. intros st f q. reflexivity. Qed.
Lemma conc_set_usage : ltac2:(zQ "60!h9!jh5!p5!jg7!pa!q3>2st$4>2sc$0>1v$0>1q$3@3$2$0@2$1@3$5^3^2^4^1@2$1^4^1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_usage : ltac2:(zQ "70!h9!iv8!p5!jg7!jge!pa!q3>2st$5>2sc$0>1v$0>1q$3@3$2$4@2$1@3$6^3^2^4^1@2$1^4^1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma oconc_set_usage : ltac2:(zQ "60!h9!jhc!p5!pa!ji4!q3>2st$3>2sc$0>1v$0>1q$4@3$2$0@2$1@3$5^3^2^4^1@2$1^4^1"). Proof. intros st sc v q. destruct q; reflexivity. Qed.
Lemma conc_set_active : ltac2:(zQ "70!h9!jh5!p5!jg7!pa!ji4!jib>2st$4>2sc$0>1v$5>1q$3@3$2$0@2$1@3$6^3^2^4^1@2$1^4^1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_active : ltac2:(zQ "80!iv8!p5!h9!jg7!jge!pa!ji4!jib>2st$5>2sc$2>1v$6>1q$3@3$1$4@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma meta_slot_set_usage : ltac2:(zQ "50!h9!jj8!jg7!pa!q3>2st$3>2sc$0>1v$0>1q$2>0@2$1^4^1@2$1@3$4^4^3^5^2"). Proof. intros st sc v q. intros H; exact H. Qed.
Lemma meta_slot_set_active : ltac2:(zQ "60!jj8!h9!jg7!pa!ji4!jib>2st$3>2sc$1>1v$4>1q$2>0@2$0^4^1@2$0@3$5^4^3^5^2"). Proof. intros st sc v q. intros H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mw_ok : ltac2:(zQ "10!jge>2mr$0P") := ltac2:(zQ "90!hk8!hp4!jk4!jl1!jle!jm9!jge!hp9!jn7\2mr$6@2$0@2$0@2$1Z@1$3^1@2$1@1$3^1+hf@2$0@2$0@2$1Z@1$2^1@2$1@1$2^1+1@2$0@2$0@2$1Z@1$5^1@2$1@1$5^1+jf@2$0@2$1Z@1$4^1@2$7@1$4^1@2$8+2+j4").

Lemma meta_word_range : ltac2:(zQ "70!jnd!hk8!jse!jge!hp4!hp9!jn7>2mr$3>0@1$2^1@2$1@2$4Z@1$0^2@2$5@1$0^2@2$6+2+k0").
Proof. intros mr. (intros nd_i1; ndestruct nd_i1 as (LI & FB & SCR & ML)). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx : ltac2:(zQ "70!p5!h9!jse!jnd!jl1!jge!jt7>2mr$5>0@1$2^1@3$0$1@2$6@1$3^2+hf@1$4^2").
Proof. intros mr.
  (intros nd_i2; ndestruct nd_i2 as (LI & FB & SCR & ML)).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_freeable : ltac2:(zQ "80!p5!h9!jse!jnd!jk4!jge!jt7!jte>2mr$5>0@1$2^1@3$0$1@2$6@1$3^2+i0@2$7+i0@1$4^2").
Proof. intros mr.
  (intros nd_i4; ndestruct nd_i4 as (LI & FB & SCR & ML)).
  assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^6) with 64. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen : ltac2:(zQ "70!p5!h9!jse!jnd!jle!jge!ju4>2mr$5>0@1$2^1@3$0$1@2$6@1$3^2+c@1$4^2").
Proof. intros mr.
  (intros nd_i5; ndestruct nd_i5 as (LI & FB & SCR & ML)).
  rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 : ltac2:(zQ "80!p5!jud!h9!jse!jnd!jle!jge!hp9>2mr$6>0@1$3^1@2$1@2$7@1$4^2+hgg0@3$0$2@1$5^2Z").
Proof. intros mr. (intros nd_i6; ndestruct nd_i6 as (LI & FB & SCR & ML)). unfold meta_word. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_word : ltac2:(zQ "b0!sd!kj9!hke!p5!h9!kk0!iv2!kk6!hjb!kl1!kld>1y$4@3$3@1$8@1$0#k0@2$7@1$0#k0@2$9@1$0#i0@2$6Z@2$a@1$0#k0@1$2@1$1^1@1$2@1$1@1$5^1").
Proof. intros y.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 : ltac2:(zQ "80!h9!hp4!jn7!p5!jt7!kmc!kk0!iv2>1f$0>1k$0>0@2$1Z^2>0@2$1Z^2@3$3$0@2$4^4@1$6@2$2+2^3@2$5^4@2$7@2$2+2^3+1").
Proof. intros f k.
  intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land. reflexivity.
Qed.



Lemma ldiff_le : ltac2:(zQ "30!hp4!h9!kmc>1f$1>1a$1>0@2$0Z^2>0@2$0Z^2@2$0@2$2^4^3^4").
Proof. intros f a.
  intros Hf Ha.
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma land_upper : ltac2:(zQ "40!hp4!h9!jt7!hk8>1f$1>1a$1>0@2$0Z^2>0@2$0Z^2@2$3@2$0Z@2$2^4^3@2$0@2$2^4^3^4").
Proof. intros f a.
  intros Hf Ha. split; [apply Z.land_nonneg; lia|].
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma le4_sxv : ltac2:(zQ "d0!sd!kqe!hk1!hk8!p5!h9!kj9!hke!hp4!hp9!jn7!kk6!hjb>1v$5>0@2$3@2$8Z^1@2$9^1@2$a+2+i0@3$4@1$2@1$c@1$0#8@1$1@2$b@1$0#k0@1$6^2@1$1@1$7^2").
Proof. intros v.
  intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
  rewrite sxv_mod32. reflexivity.
Qed.

Lemma le1_lit : ltac2:(zQ "d0!sd!hjb!kr5!hk1!krc!hk8!p5!h9!ioe!ks2!hp4!hp9!kk6>1z$7>0@2$5@2$aZ^1@2$b^1+hg0@3$6@1$3@1$1@1$0#8@1$9@2$c@1$0#k0^2@3$2@1$1@1$0#8@1$8^2@1$4@1$1@1$0#8").
Proof. intros z.
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma sllw1_word : ltac2:(zQ "e0!sd!hk8!p5!h9!kj9!hke!hp4!hp9!ks9!jn7!kt2!kk6!hjb!kl1>1i$3>0@2$1@2$6Z^1@2$7^1+i0@3$2@1$c@1$0#k0@2$b@1$0#k0@2$d@1$0#i0@2$a+1@2$8^2+i0@1$5@1$4@2$9+2^2").
Proof. intros i.
  intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero : ltac2:(zQ "91!h9!hk8!p5!kj9!hp4!ktb!hp9!jn7!jud&@2$1@2$4Z^2@2$6^2@2$7+2+i0>1f$0>1a$0>0~0>0~0@2$8@3$2$0@2$5@1$3^4@1$3^3Z@3$2$0@2$5^4^3Z").
Proof. intros f a.
  intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
  rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

(* [comment removed for export] *)
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
(* [comment removed for export] *)
