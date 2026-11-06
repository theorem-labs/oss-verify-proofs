(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jb7bounces37Corelib4Init5Logico32eqjb6mstatejbaset_bounce46Stdlib6ZArith6BinInt1Zr23eqb04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~t68bouncess35stdpp9bitvectorbdefinitionshi32bvhc4listo33andt62b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hl83updr22ler22ltr26to_natjb4ghdrhc4Somehc6optionjb4aptrjb9del_groupjb6g_metajb9get_groupjb9put_groupjbh4set_group_active_idxjb4optr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocKit_AB~~~~~~ih65mw_okt69meta_wordjbam_last_idxjb4metar26modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~iod3sxvr23powjb9mask_uptor24lxorjbbm_sizeclassr24landr23mulr26shiftrjb9span_loophc3natr23addr26of_nathc4conshc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jk53le1hi37Z_to_bvr23opphi38bv_swrapr24even" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bounces_set : ltac2:(zQ "70!h9!j4!n9!p7!pc!q5!sa>2st$4>1i$0>1v$0>1j$0@3$3$0@2$2@3$5^3^2^4^1M1\0$1$0@2$6^1^3^2@2$2^4^1").
Proof. intros st i v j.
  unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bouncess_set : ltac2:(zQ "e0!t0!h9!hh8!hk0!hk6!hkd!p7!hl3!hp2!pc!q5!hp9!hpe!hq3>2st$9>1i$1>1v$1>0@2$5@2$bZ^2@2$c^2+i0@3$6@1$4@1$3@1$0#8@1$2@3$a^3^2^4@4$8@1$3@1$0#8@1$2^4@1$d^3@1$7^2").
Proof. intros st i v.
  intros Hi. unfold bouncess.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite bounces_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma set_group_ai_eq : ltac2:(zQ "c0!hqc!p7!pc!hr3!hra!h9!hs3!hsa!ht6!htf!hub!hv7>2st$2>1b$6>2gh$0>2ai$5>0@3$1@1$4$0@2$9^4^3@2$3$0^2@3$1$2@3$b^4^2^5@4$a^4@1$8^3^2@2$7^4^5").
Proof. intros st b gh ai.
  intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
  rewrite insert_delete_eq. reflexivity.
Qed.

Lemma put_group_del : ltac2:(zQ "70!pc!hub!p7!h9!hs3!hsa!igf>2st$0>1b$4>2mo$6>2ai$3@3$2$0@4$1^3^2^1@2$5^3^4@4$1^3^2^1^4").
Proof. intros st b mo ai. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma meta_word_mod32 : ltac2:(zQ "70!p7!h9!ilb!im4!in0!ind!io4>2mr$5>0@1$2^1@3$0$1@2$6@1$3^2+i0@1$4^2").
Proof. intros mr. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sxv_inj : ltac2:(zQ "71!h9!hkd!p7!it3!hp9!hpe!ita&@2$1@2$4Z^2@2$5^2@2$6+2+i0>1a$0>1b$0>0~0>0~0>0@3$2$0@1$3^4@1$3^3@3$2$0^5^4").
Proof. intros a b.
  intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
  rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.

Lemma mask_upto_range : ltac2:(zQ "60!hkd!iu0!hp9!hpe!h9!ita>1k$4>0@2$0@2$2Z^1@2$2^1+hf@2$0@2$3Z@1$1^2@2$3@1$1^2@2$5+2+i0").
Proof. intros k.
  intros Hk. unfold mask_upto. split.
  - assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
  - assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma lxor_range31 : ltac2:(zQ "61!hkd!hp9!hpe!ita!h9!iuc&@2$0@2$1Z^2@2$2^2@2$3+2+hf>1a$4>1b$4>0~0>0~0@2$0@2$1Z@2$5^4^3@2$2@2$5^4^3@2$3+2+hf").
Proof. intros a b.
  intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
  assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.


Lemma meta_word_sc2 : ltac2:(zQ "90!p7!h9!ilb!im4!iv3!ind!jg1!jg8!jge>2mr$5>0@1$2^1@3$0$1@2$6@2$8@1$3^2+5+ne@2$7+2@1$4^2").
Proof. intros mr.
  intros MW. pose proof (meta_word_sc mr MW) as E. npose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range mr MW) as WR.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
    replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.

Lemma span_loop_bounds : ltac2:(zQ "70!h9!jh7!hp9!ji3!hkd!ji9!jif>1F$3>3cnt$0>4span$0>4size$0@2$4@2$2^3@4$1^4^3^2^1@2$2@4$1^4^3^2^1@2$5^3@1$6^4").
Proof. intros F.
  induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
  rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.

(* [comment removed for export] *)
Lemma le1_mod : ltac2:(zQ "b0!t0!hk0!jj8!hk6!jjf!p7!h9!hl3!jnf!io4!jo6>1z$6@3$5@1$3@1$1@1$0#8@1$8@2$a@1$0#k0^1@3$2@1$1@1$0#8@1$7@2$9^1+hg0@1$4@1$1@1$0#8").
Proof. intros z.
  unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.

Lemma land31_range : ltac2:(zQ "40!jg1!hp9!hkd!h9>1x$3@2$2@2$1Z@2$0^1+hf@2$1@2$0^1+hf+hf").
Proof. intros x.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.

Lemma swrap32_small : ltac2:(zQ "90!h9!ita!hkd!p7!t0!hp9!hpe!jp1!jp7>1z$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
Proof. intros z.
  intros. rewrite swrap32_eq'.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land1_mod2 : ltac2:(zQ "40!h9!p7!jg1!io4>1a$0@3$1$0@2$2^1+1@2$3^1+2").
Proof. intros a. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma even_of_land1 : ltac2:(zQ "60!j4!p7!h9!sa!jq3!jg1>1a$2@3$1$0@1$4^1@2$3@2$5^1+1Z").
Proof. intros a.
  rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.
(* [comment removed for export] *)
