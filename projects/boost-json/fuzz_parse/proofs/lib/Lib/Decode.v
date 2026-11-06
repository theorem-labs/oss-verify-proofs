(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc2le37Corelib4Init5Logicj92eq04Npos3h5LinuxProcessSemanticsfLinuxProcessSem5Statel89errno_retl8atwo_pow_64hc3sub35stdpp9bitvectorbdefinitionsq5bbv_unsignedq52bv37Corelib4Init9Datatypest54listt54prodt54boolt54truej93iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~hgfalistNN_eqbt56optionhc3powt54Nonet54Somehc3lebj93andhgf8errno_ofq57Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~hp94respt53natl87MemCopyt55falsel8aeff_copiesl8beff_copyinsl8dSyscallEffecthgf5no_cchgf8dec_brk079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~ij54eff0hc2ltl8fpage_round_up_Zt54pairhc3ltbt53nilt54cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iqa2wahgf7brk_anst54andbhc3eqbhgf8BrkGrownhgf7BrkSamehgfdbrk_new_pageshgf8zeros_ofl89mkEffectUhgf7dec_brkt53fstt53orbt53snd36Stdlib5Lists4Listjlf7forallbhc3addhgf8mmap_lenl89page_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jpb5hceilhgf6avoidshc6modulohgf8mmap_ans3h5LinuxProcessSemantics5Riscv7Preludejve6bv_eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode2HC~~~~~~kiecmmap_addr_okhgf5MmErrhgf4MmOkkie8dec_mmapij56efferrkieddec_mmap_nonehgf9range_anshgf6RgDonehgf5RgErrhgfadec_munmaphgfcdec_mprotect" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma errno_ret_unsigned : ltac2:(zQ "80!h9!j4!kd!l2!o6!p2!pf!s2>1e$0>0@2$1+1^1>0@2$1^2+vvf@3$2$0@2$7@1$3#k0@1$4^3@2$6$5^3").
Proof.
  intros e H1 H2. unfold errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false
  end.

Lemma listNN_eqb_eq : ltac2:(zQ "92!l2!t0!ud!v4!kd!vb!hg2!hg9!hkc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2l1~1>2l2~1@2$7@3$4$5@2$8^2^1$6@3$4~1^2^1").
Proof.
  induction l1 as [|[a1 n1] r1 IH]; destruct l2 as [|[a2 n2] r2]; cbn;
    try (split; congruence).
  rewrite !Bool.andb_true_iff, !bv_eqb_eq, IH.
  split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

(* [comment removed for export] *)
Definition errno_of : ltac2:(zQ "40!hla!l2!h9!t0>1r@1$3@1$1#k0@1$0$2") := ltac2:(zQ "b0!l2!h9!vb!hm3!pf!s2!hm9!hn0!hla!hn7!t0\1r@1$a@1$0#k0M2\0$2@1$8$1@2$9@2$4@2$3+2+k0+vvf@2$5@1$0#k0^1@2$7$1@2$4@2$3+2+k0@2$5@1$0#k0^1@1$6$1").

Lemma errno_of_Some : ltac2:(zQ "a0!h9!hnd!kd!l2!j4!t0!hn0!hla!o6!ho3>1r@1$5@1$3#k0>1e$0>0@3$2@1$7$0@1$9^2@2$6$0^1@2$1@3$2@1$5@1$3#k0^3@1$8^2@2$1@2$4+1^2@2$4^2+vvf").
Proof.
  intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
  split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma errno_of_errno_ret : ltac2:(zQ "80!h9!j4!hn0!hla!hnd!kd!o6!ho3>1e$0>0@2$4@2$1+1^1@2$1^1+vvf@3$5@1$3$0@1$7@1$6^2@2$2$0^2").
Proof.
  intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
  destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

Lemma errno_of_small : ltac2:(zQ "b0!l2!h9!hm9!hla!kd!ho3!j4!hm3!pf!t0!s2>1r@1$9@1$0#k0>0@2$6@2$a@1$0#k0^1@2$8@2$7+2+k0+hgg0@3$4@1$3$1@1$5^2@1$2$1").
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Lemma errno_of_lit : ltac2:(zQ "b0!h9!j4!hm9!hla!hnd!kd!l2!ho3!hm3!pf!hof>1z$0>0@2$4@2$1Z^1@2$1^1@2$9@2$8+2+k0+hgg0@3$5@1$3$0@1$7@2$a@1$6#k0^2@1$2$0").
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

(* [comment removed for export] *)
Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

(* [comment removed for export] *)
Definition no_cc : ltac2:(zQ "20!vb!ht5>3rsp$1$0") := ltac2:(zQ "c0!ud!htd!v4!l2!hu3!t0!vb!hud!hg2!hv5!ig2!ht5\3rsp$bM0\1x@1$0$4$6@1$9^1M0\1x@1$0@2$2@1$5@1$3#k0$1$6@1$a^1$8\1p@2$2@1$5@1$3#k0$1\1l@1$0@2$2@1$5@1$3#k0$1$7\1m$4\1l@1$0$4$7").

Ltac dec_cc cs ci H := cbn [no_cc eff_copies eff_copyins] in H; destruct cs; [|discriminate H]; destruct ci; [|discriminate H]; cbv iota in H.

(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dec_brk0 : ltac2:(zQ "30!hla!h9!ht5>3rsp$2@1$0$1") := ltac2:(zQ "f6!l2!t0!ud!v4!h9!hla!hm9!vb!ih0!hn0!htd!hu3!ii0!ht5!s2&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&\1l~3@1$6$4&\1p~2~4\3rsp$dM7\0$7@1$5$4@1$c^1M8\3rsp$8@1$5$4^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$b\beff_copyins@1$2@2$3@1$1@1$0#k0$aM2\aeff_writes~1@1$5$4^5M2\9eff_zeros~3@1$5$4^4M2\aeff_unmaps~3@1$5$4^3@2$9$4@2$e@1$0#k0^6~5~5\1p~0\1l~1@1$6$4@1$6$4").

Lemma dec_brk0_Some : ltac2:(zQ "d0!h9!hnd!kd!ht5!hn0!hla!l2!ii9!in1!j4!in9!hm3!hof>3rsp$3>1b$0>0@3$2@1$5$0@1$7^2@2$4$0^1@2$1@3$2$3^3@1$8@2$c@1$6#k0^2@2$1@2$9Z^2@2$a^2@2$b+2+k0").
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition brk_new_pages : ltac2:(zQ "30!h9!hla!v4>3cur$0>3req$0@1$1@2$2$0$0") := ltac2:(zQ "a0!h9!v4!vb!ine!hm9!hn0!hla!ip0!ip7!pf\3cur$0\3req$0=2lo$0@1$3^2=2hi$0@1$3^2M2\0$2@1$6@2$1$0$0@2$8^2^1@2$5@2$1$0$0@4$7$0$0^2@2$9^1^2@1$4@2$1$0$0").

Definition zeros_of : ltac2:(zQ "60!v4!l2!h9!t0!ud!hla>1p@1$5@2$0$2$2@1$4@2$0@1$3@1$1#k0@1$3@1$1#k0") := ltac2:(zQ "b3!l2!t0!v4!h9!hla!ud!ipd!iq3!ip0!iu4!hof&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0&@1$6~0\1p@1$4@2$2$3$3M4\1p@1$4@2$2$3$3~1^1\2p0@2$2$3$3M2\2p0@2$2$3$3~1^1\2lo$3\1n$3@3$7~0@4$8@1$1@1$0#k0@1$1@1$0#k0@1$9^2@2$a@1$0#k0^1~2~2").

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk : ltac2:(zQ "40!h9!hla!iua!ht5>3cur$0>3req$0>3rsp$3@1$1$2") := ltac2:(zQ "h94!l2!t0!ud!v4!iua!vb!hla!hm9!hn0!iv5!h9!ih0!ivc!s2!hud!htd!hg2!hu3!jg2!jge!jh9!hkc!ii0!jia!ht5&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\3cur$a\3req$a\3rsp$h8M5\0$5@1$6$4@1$h6^1Mb\3rsp$b@1$6$4^1\1r@1$1@1$0#k0\aeff_writes~1\2zs~3\aeff_unmaps~3\aeff_copies@1$2$h1\beff_copyins@1$2@2$3@1$1@1$0#k0$fM2\aeff_writes~1@1$6$4^5M2\aeff_unmaps~3@1$6$4^3M5\0$5@1$6$4@2$9@2$c@2$d@1$0#k0^6^9M2\2zs~3$5^4$h0\1p~2\1l~3$e@2$8$4$h3M5\0$5@1$6$4@2$9@2$c@2$d@1$0#k0^6^8@2$h5^4@1$h7@2$h4^9^8@2$8$4$h2@1$7$4\1p~2\1l~3@1$7$4\1p~0\1l~1@1$7$4@1$7$4").

Lemma dec_brk_Some : ltac2:(zQ "h30!l2!iua!t0!ipd!v4!kd!ht5!h9!hof!hn0!ud!htd!hla!hu3!jj6!jh9!jk2!jia!in1>3cur$7>3req$7>3rsp$6>1a$1>0@3$5@1$c$1@3$h0^4^3^2@2$9$1^1M1\1a$1P^2@3$5$6^3@6$e@2$8@1$0#k0^4@1$3@2$4@1$2@1$0#k0@1$a@1$2@1$0#8@1$h1@2$f^5^4@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$3$d@1$3@2$4@1$2@1$0#k0$b@3$5$6^3@1$h2@2$8@1$0#k0^5").
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Definition CEIL_MIN : Z := 0x7fff7f800000.
Definition CEIL_MAX : Z := 0x7fffff800000.
Definition CEIL_BAND : Z := 0x800000000000.
Definition alloc_ceiling : Z := 0x7fffff800000.

(* [comment removed for export] *)
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids : ltac2:(zQ "40!h9!vb!ud!v4>1a$0>1n$0>5avoid@1$2@2$3$0$0$1") := ltac2:(zQ "90!h9!v4!hn7!jkd!ud!jl3!jl9!jn2!jnd\1a$0\1n$0\5avoid@1$4@2$1$0$0@3$7@2$1$0$0\2iv@2$1$0$0@2$5@2$2@2$8^4^3@3$3$0$0^1@2$2@3$6$0$0^1^4^1").

Definition mmap_len : ltac2:(zQ "10!h9>3len$0$0") := ltac2:(zQ "20!h9!ine\3len$0@1$1^1").

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

Definition mmap_addr_ok : ltac2:(zQ "40!h9!vb!ud!v4>3len$0>5avoid@1$2@2$3$0$0>1a$0$1") := ltac2:(zQ "d0!h9!iv5!jo3!ud!v4!jof!jt6!jtf!jnd!ivc!hn7!ip7!ju9\3len$0\5avoid@1$3@2$4$0$0\1a$0@2$1@2$1@2$1@2$9@2$c^1$5Z@2$bZ^1@2$a@2$8^1@1$2^3@1$6?2HC@3$7^1@1$2^3^2").

Definition dec_mmap : ltac2:(zQ "60!h9!ud!hla!v4!jv2!ht5>3len$0>5avoid@1$1@2$3$0$0>3rsp$5@1$2$4") := ltac2:(zQ "h87!l2!t0!ud!v4!jv2!hla!hm9!h9!vb!hn0!iv5!ih0!ki4!s2!htd!hu3!kme!kne!ko7!ho3!jo3!ii0!ht5!hof&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&\aeff_unmaps~3@1$5$4&\2l0~3@1$6$4&\2p0~2~5\3len$7\5avoid@1$2@2$3$7$7\3rsp$h6M8\0$8@1$5$4@1$h5^1Mb\3rsp$b@1$5$4^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$f\beff_copyins@1$2@2$3@1$1@1$0#k0$eM2\aeff_writes~1@1$5$4^5M2\9eff_zeros~3@1$5$4^4M2~4^3M5\1x@1$5$7@1$5$4@1$h3^6\1e$7@2$9$4@1$h1^1@1$6$4\1p~2\1l~3@1$6$4\1p~2\1l~3M3\1p~2@1$5$4^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0M2\1l~3@1$5$4^3M2~4^7M8\0$8@1$5$4@2$a@2$a@3$c@1$0#k0^2^a@3$c@1$0#k0^1@2$h7@1$0#k0@1$h4^d@3$h0^d^c@2$d@1$0#k0^a@2$9$4@1$h2@2$d@1$0#k0^a@1$6$4~6~6\1p~0\1l~1@1$6$4@1$6$4").

Definition dec_mmap_none : ltac2:(zQ "60!h9!ud!hla!v4!jv2!ht5>3len$0>5avoid@1$1@2$3$0$0>3rsp$5@1$2$4") := ltac2:(zQ "h84!l2!t0!ud!v4!jv2!hla!hm9!h9!vb!hn0!iv5!ih0!ki4!s2!htd!hu3!kme!kne!ko7!ho3!jo3!ii0!ht5!hof&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\3len$7\5avoid@1$2@2$3$7$7\3rsp$h6M8\0$8@1$5$4@1$h5^1Mb\3rsp$b@1$5$4^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$f\beff_copyins@1$2@2$3@1$1@1$0#k0$eM2\aeff_writes~1@1$5$4^5M2\9eff_zeros~3@1$5$4^4M2\aeff_unmaps~3@1$5$4^3M5\1x@1$5$7@1$5$4@1$h3^6\1e$7@2$9$4@1$h1^1@1$6$4\1p~2\1l~3M3\1p~2@1$5$4^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0M2\1l~3@1$5$4^3M8\0$8@1$5$4@2$a@2$a@3$c@1$0#k0^2^a@3$c@1$0#k0^1@2$h7@1$0#k0@1$h4^d@3$h0^d^c@2$d@1$0#k0^a@2$9$4@1$h2@2$d@1$0#k0^a@1$6$4\2p0~2\2l0~3@1$6$4\1p~2\1l~3@1$6$4\1p~0\1l~1@1$6$4@1$6$4").

Lemma mmap_addr_ok_true : ltac2:(zQ "h00!h9!hnd!kd!vb!hg2!jo3!ud!v4!jof!jt6!kme!jtf!jnd!j4!in9!ju9>3len$0>5avoid@1$6@2$7$0$0>1a$0>0@3$2$3@3$a^3^2^1$4@2$1@2$1@3$2$0@2$f^2$8Z@2$1@2$eZ^2@2$d@2$c^2@1$5^4@1$9?2HC@3$2$3@3$b^2@1$5^4^3$4").
Proof.
  intros len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : ltac2:(zQ "ha2!l2!t0!v4!ipd!h9!jv2!kd!hnd!ht5!ud!j4!hof!hn0!vb!iq3!htd!hla!ip0!hg2!hu3!jj6!kof!kme!jo3!iu4!kpb&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>3len$4>5avoid@1$9@2$2$4$4>3rsp$8>1x$5>0@3$6@1$h0$5@3$h5^4^3^2@2$c$5^1M5\1x$5P^2\1e$4@2$7@3$6$8^4@1$h9^1@2$7@2$a+1^1@2$a^1+vvf\1a$4@2$7@3$6$8^4@6$h4@2$b@1$0#k0^1@1$3@2$2@1$1@1$0#k0@1$9@1$1@1$0#8@3$e~0@4$h1@1$1@1$0#k0@1$1@1$0#k0@1$h8^1@2$b@1$0#k0@1$h7^6~1~1@1$3$h3@1$3@2$2@1$1@1$0#k0$f@3$6$d@3$h6^6^5^1$h2").
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : ltac2:(zQ "ha2!l2!t0!v4!ipd!h9!jv2!kd!hnd!ht5!ud!j4!hof!hn0!vb!iq3!htd!hla!ip0!hg2!hu3!jj6!kq5!kme!jo3!iu4!kpb&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>3len$4>5avoid@1$9@2$2$4$4>3rsp$8>1x$5>0@3$6@1$h0$5@3$h5^4^3^2@2$c$5^1M5\1x$5P^2\1e$4@2$7@3$6$8^4@1$h9^1@2$7@2$a+1^1@2$a^1+vvf\1a$4@2$7@3$6$8^4@6$h4@2$b@1$0#k0^1@1$3@2$2@1$1@1$0#k0@1$9@1$1@1$0#8~1@3$e~0@4$h1@1$1@1$0#k0@1$1@1$0#k0@1$h8^1@2$b@1$0#k0@1$h7^6~1@1$3$h3@1$3@2$2@1$1@1$0#k0$f@3$6$d@3$h6^6^5^1$h2").
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.
End HC.

(* [comment removed for export] *)
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap : ltac2:(zQ "40!h9!hla!kr6!ht5>4addr$0>3len$0>3rsp$3@1$1$2") := ltac2:(zQ "ha4!l2!t0!ud!kr6!v4!hla!hm9!vb!h9!hn0!iv5!ih0!ki4!ks3!ivc!hof!s2!hud!htd!hg2!hu3!ksd!ho3!jo3!ii0!ht5&@2$4@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\4addr$8\3len$8\3rsp$h9M7\0$7@1$5$3@1$h8^1Mb\3rsp$b@1$5$3^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$h4\beff_copyins@1$2@2$4@1$1@1$0#k0$h2M2\aeff_writes~1@1$5$3^5M2\9eff_zeros~3@1$5$3^4M2\aeff_unmaps~3@1$5$3^3M5\1x@1$5$8@1$5$3@1$h6^6\1e$8@2$9$3@1$h5^1M7\0$7@1$5$3@2$e@2$h0@1$0#k0^6Z@2$9$3@1$d$h1@1$6$3\1p~2\1l~3M4\1p~2@1$5$3^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0M2\1l~3@1$5$3^3M7\0$7@1$5$3@2$a@2$a@2$e@2$h0@1$0#k0^aZ@3$c@1$0#k0^2@2$f@1$0#k0^d@3$c@1$0#k0^1@2$f@1$0#k0@1$h7^c@2$9$3@1$d$h3@1$6$3\2p0~2\2l0~3@1$6$3\1p~2\1l~3@1$6$3\1p~0\1l~1@1$6$3@1$6$3").

Definition dec_mprotect : ltac2:(zQ "40!h9!hla!kr6!ht5>4addr$0>3len$0>3rsp$3@1$1$2") := ltac2:(zQ "ha7!l2!t0!ud!v4!kr6!hla!hm9!vb!h9!hn0!iv5!ih0!ki4!ks3!ivc!hof!s2!hud!htd!hg2!hu3!ksd!ho3!jo3!ii0!ht5&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&\aeff_unmaps~3@1$5$4&\2l0~3@1$6$4&\2p0~2~5\4addr$8\3len$8\3rsp$h9M7\0$7@1$5$4@1$h8^1Mb\3rsp$b@1$5$4^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$h4\beff_copyins@1$2@2$3@1$1@1$0#k0$h2M2\aeff_writes~1@1$5$4^5M2\9eff_zeros~3@1$5$4^4M2~4^3M5\1x@1$5$8@1$5$4@1$h6^6\1e$8@2$9$4@1$h5^1M7\0$7@1$5$4@2$e@2$h0@1$0#k0^6Z@2$9$4@1$d$h1@1$6$4\1p~2\1l~3@1$6$4\1p~2\1l~3M3\1p~2@1$5$4^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0M2\1l~3@1$5$4^3M2~4^7M7\0$7@1$5$4@2$a@2$a@2$e@2$h0@1$0#k0^aZ@3$c@1$0#k0^2@2$f@1$0#k0^d@3$c@1$0#k0^1@2$f@1$0#k0@1$h7^c@2$9$4@1$d$h3@1$6$4~6~6\1p~0\1l~1@1$6$4@1$6$4").

Lemma dec_munmap_Some : ltac2:(zQ "h82!l2!t0!ipd!v4!kr6!kd!ht5!hof!vb!h9!hnd!j4!hn0!iq3!ud!htd!hla!ip0!hu3!jj6!kt6!jo3!in1!kpb&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4addr$9>3len$9>3rsp$6>1x$4>0@3$5@1$h0$4@3$h4^4^3^2@2$c$4^1M4\1x$4P^2\1e$9@2$a@3$5$6^4@1$h7^1@2$a@2$b+1^1@2$b^1+vvf\7changed$8M8\7changed$8P^1@3$5$6^4@6$h3@2$7@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$e@1$1@1$0#8~1@3$d~0@4$h1@1$1@1$0#k0@1$1@1$0#k0@2$7@1$0#k0^6@2$7@1$0#k0@1$h5^5~1@1$2$h2@1$2@2$3@1$1@1$0#k0$f@3$5$6^4@1$h6@2$7@1$0#k0Z").
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_mprotect_Some : ltac2:(zQ "h82!l2!t0!ipd!v4!kr6!kd!ht5!hof!vb!h9!hnd!j4!hn0!iq3!ud!htd!hla!ip0!hu3!jj6!ku4!jo3!in1!kpb&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4addr$9>3len$9>3rsp$6>1x$4>0@3$5@1$h0$4@3$h4^4^3^2@2$c$4^1M4\1x$4P^2\1e$9@2$a@3$5$6^4@1$h7^1@2$a@2$b+1^1@2$b^1+vvf\7changed$8M8\7changed$8P^1@3$5$6^4@6$h3@2$7@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$e@1$1@1$0#8@3$d~0@4$h1@1$1@1$0#k0@1$1@1$0#k0@2$7@1$0#k0^6@2$7@1$0#k0@1$h5^5~1~1@1$2$h2@1$2@2$3@1$1@1$0#k0$f@3$5$6^4@1$h6@2$7@1$0#k0Z").
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate].
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
