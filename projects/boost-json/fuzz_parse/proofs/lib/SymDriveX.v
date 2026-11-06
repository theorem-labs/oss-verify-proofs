(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~06kentry37Corelib4Init9Datatypesk74listk76option37Corelib7Numbers7BinNumsmf4Npos35stdpp9bitvectorbdefinitionsof2bvk74Somek73nat37Corelib4Init5Logicre2eq3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypet77Segment03env79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~hhb9kentry_okhhb7know_ok36Stdlib5Lists4Listhn89nth_errork73appre3andre3iffk74consk74bool04exprmf1Zk75false05saddr08expr_eqbk74andb46Stdlib6ZArith6BinInt1Zhu23addhu23leb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ig83rdnhu26of_natof7Z_to_bvofbbv_unsigned37Corelib4Init5Peanoimc2lthu22lek74Nonehu22lthu23pow04KImg02SAk74true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsir18store_ok03KWr06adenot06sentrymf8positive3h5LinuxProcessSemantics5Riscv5Instrjh45aluopjh45mulop46Stdlib5Arith8PeanoNat3Natjka3eqbhu23opp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9SymDriveX4FPX1~~~~~~jn3dentry_below_bhn87forallb02ev02SEjn3blog_below_bhhb9mem_denotk76length37Corelib5Lists7ListDefjvd3nth04ELit06edenothhb7regs_ok3h5LinuxProcessSemantics5Riscv7Preludekj45bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~km39junk_vals69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~kqb7vals_ev37Corelib4Init3Natkuf3add03Envkqbakn_vars_ltkqbasr_vars_ltig84getrhn82Inre1Ire3notjvd3mapkm3fsr_after_call_j04ridxof2BVof4BvWf08sidecondk73nilk74prodk74pairimc2leir1h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~lq66wbytes05carryhhb4flatir18is_ecalljn36ECALLWjh47ALU_ADD04EAlu69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~mi0bcallee_kept" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma know_nth : ltac2:(zQ "d0!jf!lf!m6!o8!qc!r1!r8!t2!hgc!hh6!hm0!hmd!hob>4segs@1$1$8>1E$9>1M>0@1$4@1$3#k0@1$2@1$4@1$3#8>2kn@1$1$0>1i$6>1K$0>0@4$b^6^5^4^3>0@3$7@1$2$0@3$c$0^4^3@2$5$0^2@4$a^8^7^6^3").
Proof.
  intros segs E M kn i K HK Hn. unfold know_ok in HK.
  apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.

Lemma know_ok_app : ltac2:(zQ "b0!lf!jf!hmd!o8!qc!hp8!m6!hpe!hq4!hgc!hh6>4segs@1$0$9>1E$a>1M>0@1$4@1$3#k0@1$6@1$4@1$3#8>2k1@1$0$1>2k2@1$0$1@2$8@4$2^5^4^3@3$5$1^2^1@2$7@4$2^5^4^3^2@4$2^5^4^3^1").
Proof. intros. unfold know_ok. apply Forall_app. Qed.

Lemma know_ok_cons : ltac2:(zQ "a0!jf!lf!o8!hmd!qc!hqa!m6!hgc!hh6!hm0>4segs@1$1$7>1E$8>1M>0@1$4@1$2#k0@1$6@1$4@1$2#8>1K$0>2kn@1$1$0>0@4$9^5^4^3^2>0@4$3^6^5^4^2@4$3^7^6^5@3$5$0^4^3").
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

(* [comment removed for export] *)
Definition is_krange : ltac2:(zQ "30!hr1!hr8!jf>1e$1>1K$2$0") := ltac2:(zQ "80!hre!hs2!hr8!hsa!jf!r8!hr1!ht1\1e$2\1K$4M4\1K$4$6^1\1a$3\1w$5\1v$2$1\1a$3\1n$2$1\1a$3\1n$2\1k$5$1\2lo$0\2hi$0$1\2e0$2\1m$0$1\2e'$2\2lo$0\2hi$0@2$7^5^3\1a$3\1n$0$1\2a1$3\2n1$0\2a2$3\2n2$0$1").
(* [comment removed for export] *)
Definition is_kwr_cov : ltac2:(zQ "40!hre!hr1!hr8!jf>1b$2>1k$0>1m$0>1K$3$1") := ltac2:(zQ "b0!hre!hsa!hs2!hr8!jf!htb!hr1!r8!hva!ig1!ht1\1b$3\1k$0\1m$0\1K$4M4\1K$4$6^1\1a$1\1w$7\1v$3$2\1a$1\1n$3$2\1a$1\1n$3\2k0$7$2\2lo$0\2hi$0$2\1e$3\2m0$0$2\1e$3\2lo$0\2hi$0$2\1a$1\3len$0M1\1a$1$6^2\1c$3\2kk$0@2$5@2$5@2$a^8^2@2$9^1^7@2$9@2$8^7^6@2$8^1^3\2a1$1\2n1$0\2a2$1\2n2$0$2").
(* [comment removed for export] *)
Definition is_kimg_cov : ltac2:(zQ "30!hre!hr1!jf>1a$0>1n$0>1K$2$1") := ltac2:(zQ "a0!hre!hs2!hsa!hr8!jf!r8!ig1!htb!hr1!hva\1a$0\1n$0\1K$4M4\1K$4$8^1\2a0$2\1w$5\1v$3$1\2a0$2\2n0$3$1\2a0$2\2n0$3\1k$5$1\2lo$0\2hi$0@2$7@2$6^2^5@2$6@2$9^5^4^1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\2n0$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_agree : ltac2:(zQ "d2!o8!qc!m6!lf!r8!t2!ik3!hva!ika!il4!ile!io0!hgc&>1x@1$1@1$0#k0@1$2@1$1@1$0#8&@2$9@1$0#k0@2$7@2$a@1$0#k0^3@1$8^2>4segs@1$3$c>1M~0>2M'~0>1n$4>1a@1$1@1$0#k0>0>1j$4>0@2$b^1^3@3$5@1$2@1$1@1$0#8@1^6~1@1^5~1@3$5@1$2@1$3@1$1@1$0#8@4$6^6^5^2^3@4$6^6^4^2^3").
Proof.
  intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_untouched : ltac2:(zQ "h10!o8!qc!m6!io6!il4!ioc!lf!t2!hre!ik3!hva!ika!r8!hpe!hgc!ip3!ip9>4segs@1$6$e>1M>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$8>1n$c>0@2$3Z^2>0@2$3@2$a^3@1$b^2@2$h0+2+k0>0>1i$8>0@2$d@2$3^5^1@2$f^1@2$a^5@1$b^4@3$7@1$2@1$1@1$0#8@1^7@2$4@1$0#k0^2@1$5@1$1@1$0#8@3$7@1$2@1$6@1$1@1$0#8@4$9^7^6@2$4@1$0#k0^5^4@4$9^7\0@1$1@1$0#k0@1$5@1$1@1$0#8@2$4@1$0#k0^5^4").
Proof.
  intros segs M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.

Lemma kimg_rdn : ltac2:(zQ "h40!o8!qc!jf!lf!m6!hre!r8!t2!ik3!io6!il4!ioc!r1!hgc!iq0!hh6!hmd!hob!hva!ika>4segs@1$3$d>1E$f>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>2kn@1$3$2>1i$6>2lo$5>2hi$5>1a$5>1n$6>0@4$h0^9^8^7^6>0@3$7@1$4$2@3$h1$2^7^6@2$c$2@2$e^5^4>0@2$9^6^4>0@2$9@2$h2^5@1$h3^4^6@3$7@1$4@1$3@1$1@1$0#8@4$8^d^b@2$a@1$0#k0^6^5@4$8^d\0@1$1@1$0#k0@1$b@1$1@1$0#8@2$a@1$0#k0^6^5").
Proof.
  intros segs E M kn i lo hi a n HK Hn Hlo Hhi.
  pose proof (know_nth segs E M kn i _ HK Hn) as (H0 & H64 & Hnone).
  apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kwr_store_ok : ltac2:(zQ "h70!jf!hre!lf!r8!m6!t2!o8!iq6!hva!io6!qc!r1!hr1!iqa!hgc!iu8!iv4!iv9!hh6!hr8!hmd!hob!ika>4segs@1$2$e>1E$h2>1M>0@1$a@1$6#k0@1$4@1$a@1$6#8>2kn@1$2$0>1i$3>1b$h3>2kk$1>3len$1>1k$1>1m$3>0@4$h4^a^9^8^7>0@3$5@1$4$0@3$h5$0^8^7@2$b$0@2$h0@2$7^6^5^4>0@2$9^6^4>0@2$9@2$8^5@1$h6^4@2$8^7^6@3$5$c@4$f^e^c@2$h1^d@2$7^9^6^5$d").
Proof.
  intros segs E M kn i b kk len k m HK Hn H1 H2.
  pose proof (know_nth segs E M kn i _ HK Hn) as (Hfl & Hst).
  unfold adenot. cbn [a_base a_off].
  ndestruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
  replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
  unfold v_addi. exact Hst.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_below_b : ltac2:(zQ "40!hr1!r8!hre!jg1>3spi$1>3ihi$2>1e$3$0") := ltac2:(zQ "h10!hr8!hs2!r8!hr1!hre!ig1!htb!hsa!jg1!jg9!jj8!jk1!hva!ika!jm5!jmc!ip9\3spi$2\3ihi$4\1e$8M8\1e$8$3^1\6e_addr$7\1w$2\5e_val$0M7\6e_addr$7$3^3\6a_base$0\1k$4M0\6a_base$0$3^2\1z$4M4\1z$4$3^1@2$6@2$5Z^2@2$5@2$c^2@1$d^5^8\1p$9$1\1p$9$1\1i$2@2$6@2$6@2$e^1^9@2$5@2$c^2@1$d^5Z@2$5@1$f@2$h0+2+i8^2\2op$a\1a$0\1b$0$1\2op$a\1a$0\1b$0$1\2op$b\1a$0\1b$0$1\2op$b\1a$0\1b$0$1\2sx$3\2lo$2\1n$2\2e0$0$1\2sx$3\2k0$2\1i$4\1n$2$1").

Definition log_below_b : ltac2:(zQ "50!hr1!lf!r8!hre!jg1>3spi$2>3ihi$3>3log@1$1$4$0") := ltac2:(zQ "60!jg1!lf!r8!hre!jr4!js5\3spi$2\3ihi$3\3log@1$1$0@3$5$0@2$4^3^2^1").

Lemma entry_below_sound : ltac2:(zQ "h30!o8!ile!io6!r8!hre!iq6!jt0!hr8!hr1!iqa!t2!jr4!jt4!iv9!hh6!hva!ika!ip9!qc>1E$e>3spi$3>3ihi$4>1b$7>1k$4>1w$3>1v$7>1x@1$h2@1$0#k0>0@3$a$8@3$b^7^6@3$c@2$5^5^4^3^2$9>0@2$2@2$h1+2+i8@2$1@1$0#k0@2$6^9^8>0@2$2@2$1@1$0#k0@2$6^a^9@2$1@1$0#k0^3>0@2$2^9@2$1@1$0#k0^4@2$2@2$f@2$1@1$0#k0@2$d^c@2$5^9^8@1$h0^7@2$1@1$0#k0^5").
Proof.
  intros E spi ihi b k w v x He Hsp Hx1 Hx2.
  unfold adenot, v_addi. cbn [a_base a_off]. pose proof (u64_range x) as Hxr.
  destruct b as [z|i| | | | | |]; cbn [entry_below_b] in He; try discriminate.
  - destruct z; try discriminate. apply andb_prop in He as [He1 He2].
    apply Z.leb_le in He1. apply Z.leb_le in He2. cbn [edenot].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l, u_small by lia. lia.
  - apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
    apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
    cbn [edenot]. pose proof (u64_range (ev E spi)) as Hs. rewrite u_small by lia. lia.
Qed.

Lemma mem_denot_above : ltac2:(zQ "h10!o8!qc!ile!io6!m6!t2!jt0!hr1!lf!r8!iqa!hre!jt8!hh6!jg1!ju7!ip9>1E$d>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>3log@1$8$e>3spi$9>3ihi$b>1x@1$1@1$0#k0>0@3$5$7@3$c^3^2^4$a>0@2$3@2$h0+2+i8@2$2@1$0#k0@2$6^7^4>0@2$3@2$2@1$0#k0@2$6^8^5@2$2@1$0#k0^3>0@2$3^5@2$2@1$0#k0^4@3$5@1$4@1$1@1$0#8@4$f^a^9^8^5@1^9^5").
Proof.
  intros E M log spi ihi x Hb Hsp Hx1 Hx2.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_below_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  pose proof (entry_below_sound E spi ihi b k w v x He Hsp Hx1 Hx2) as Hbnd.
  pose proof (u64_range x) as Hxr.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. lia.
  - rewrite length_N_to_le_bytes. right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_ext : ltac2:(zQ "e0!hr8!jv4!o8!lf!r8!t2!kh4!khb!ki1!ki9!qc!io0!kla!hh6>1E$d>2sr@1$3$0>3sr'@1$3$0>1R@2$c@1$2#5@1$a@1$2#k0>0@3$5$4@2$1$0^3@2$1$0^2>0>1i$4>0@2$b^1@2$1$0^5@3$5@1$a@1$2#k0@2$8^7@4$6$0^2^6@1$7Z@2$8^7@4$6$0^2^5@1$7Z>0@3$9^6^5^3@3$9^7^5^4").
Proof.
  intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
  - apply Heq. exact Hlt.
  - rewrite !nth_overflow by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma junk_vals_length : ltac2:(zQ "70!o8!qc!jv4!r8!t2!kla!kpe>1R@2$5@1$0#5@1$1@1$0#k0@3$4$3@2$2@1$1@1$0#k0@1$6^1Ni0").
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

Lemma vals_ev_app_l : ltac2:(zQ "90!o8!qc!lf!ku4!hp8!jv4!r8!t2!io0>4vals@1$2@1$1@1$0#k0>5extra@1$2@1$1@1$0#k0>1n$6>0@2$8^1@2$5@1$1@1$0#k0^3@3$7@1$1@1$0#k0@2$3@3$4@1$1@1$0#k0^4^3^2@2$3^4^2").
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.

Lemma vals_ev_app_r : ltac2:(zQ "90!o8!qc!lf!ku4!hp8!jv4!r8!t2!lg1>4vals@1$2@1$1@1$0#k0>5extra@1$2@1$1@1$0#k0>1n$6@3$7@1$1@1$0#k0@2$3@3$4@1$1@1$0#k0^3^2@2$8@2$5@1$1@1$0#k0^3^1@2$3^2^1").
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.

(* [comment removed for export] *)
Lemma env_app_know : ltac2:(zQ "h00!o8!qc!lf!lg8!hmd!ku4!hp8!hr1!jv4!r8!m6!iqa!t2!hgc!jf!lgd>4segs@1$2$d>4vals@1$2@1$1@1$0#k0>5extra@1$2@1$1@1$0#k0>3ebs>0$9@1$2@1$1@1$0#8>1M>0@1$1@1$0#k0@1$a@1$1@1$0#8>2kn@1$2$e>0@3$c$7@2$f@2$8@1$1@1$0#k0^5^1$b>0@4$4^7@2$3@1$5^6^4^3^2@4$4^8@2$3@1$5@3$6@1$1@1$0#k0^7^6^5^4^3").
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_regs : ltac2:(zQ "f0!o8!qc!lf!lg8!ki9!ku4!hp8!hr1!jv4!r8!iqa!t2!kla!hr8!lhb>4vals@1$2@1$1@1$0#k0>5extra@1$2@1$1@1$0#k0>3ebs>0$9@1$2@1$1@1$0#8>2sr@1$2$d>1R@2$c@1$0#5@1$1@1$0#k0>0@3$b$7@2$e@2$8@1$1@1$0#k0^5^2$a>0@3$4@2$3@1$5^6^4^3^2@3$4@2$3@1$5@3$6@1$1@1$0#k0^7^6^5^4^3").
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

(* [comment removed for export] *)
Lemma regs_after_keeps : ltac2:(zQ "h90!o8!qc!lf!jv4!r8!t2!kla!li9!lg8!ki9!ku4!lj1!hp8!hr1!iqa!lj7!ljb!lk1!kpe!lk8!hr8!llb!lhb!lm1!lm6>4vals@1$2@1$1@1$0#k0>3ebs>0$4@1$2@1$1@1$0#8>2sr@1$2$h4>1R@2$6@1$0#5@1$1@1$0#k0>2R'@2$6@1$0#5@1$1@1$0#k0>4kept@1$2@1$1@1$0#5>0@3$5$d@2$h6@2$3@1$1@1$0#k0^6^4$e>0@3$9@2$8@1$a^7^6^5^4>0>1r@1$1@1$0#5>0@3$b@1$1@1$0#5^1^4@3$5@1$1@1$0#k0@2$7^6^2@2$7^7^2>0@1$h0@3$b@1$1@1$0#5@3$h7@1$0#5ZKv$f@2$h8@1$0#5Z^4@3$9@2$8@1$a@3$c@1$1@1$0#k0^a@1$h2^6^9@3$h3^8@4$h1@1$1@1$0#5$4$h5^5@2$3@1$1@1$0#k0^a^6").
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk H0.
  apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
  - intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
    rewrite ridx_roundtrip. apply Hk. exact Hr.
  - intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
    replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma know_after_store : ltac2:(zQ "hc0!lf!lmd!jf!hr1!o8!qc!ln7!lnd!t2!lo4!jg1!hmd!hqa!r8!m6!lob!hgc!lp1!lu0!jt4!iv9!lua!ki1!hh6!hr8!hsa!lv1!ika>4segs@1$0$h0>1E$h7>1M>0@1$5@1$4#k0@1$e@1$5@1$4#8>2kn@1$0$2>2sa$h9>1w$d>1v$h8>2bs@1$0@1$5@1$4#8>3kn'@1$0$2>3scs@1$0$1>2hs@1$0$3>0@3$8@2$7@2$7@1$0$2@1$0$1@1$0$3@3$h5@3$c$a@3$h3^7^6^5@1$6$a^8@1$6$3@4$9@2$7@1$0$2@1$0$1@1$0$3@4$9@1$0$2@1$0$1^3^2^1>0@3$8@1$0$1^3@1$6$1>0@4$b^d^c^b^a>0@2$f^9N8>0@3$ha^e^b@1$hb^a>0@3$8@1$0@1$5@1$4#8^9@2$h1^b@2$h6^f^a@4$b^h1^h0@3$h2^f@2$h4^h0^d^a^9").
Proof.
  intros segs E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
  change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
  eapply carry_after; [exact Hc | | exact HK | constructor].
  cbn [log_flat]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma flat_intro : ltac2:(zQ "c0!hva!o8!ki1!io6!ile!hre!ip9!iq6!hh6!hr8!lv1!ip3>1E$8>1b$9>1k$5>1n$5>0@2$3Z@2$0@2$4@1$1#k0@2$2^4^3^2>0@2$3Z^2>0@2$b@2$0@2$4@1$1#k0@2$2^6^5^4@2$6+2+k0>0@2$3@2$0@2$0@2$4@1$1#k0@2$2^7^6^5^4@2$6+2+k0@3$a^8@2$7^7^6^5").
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ECALLW : ltac2:(zQ "20!o8!qc@1$1@1$0#i0") := ltac2:(zQ "20!o8!il4@2$1@1$0#i0+n3").
Lemma is_ecall_ECALLW : ltac2:(zQ "50!hr1!iqa!t2!lv9!mg5@3$2$0@1$3$4$1"). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adenot_lit0 : ltac2:(zQ "90!o8!t2!hre!khb!iq6!iv9!hh6!il4!qc>1E$6>1a$2@3$1@1$8@1$0#k0@2$5^2@2$4@1$3Z^1@2$7@1$0#k0^1").
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.

Lemma edenot_add_lit : ltac2:(zQ "c0!t2!o8!hre!mgf!mha!khb!iq6!iv9!ki1!hh6!hr8!qc>1E$9>1b$a>1k$2@3$0@1$b@1$1#k0@2$8^3@3$4$3^2@1$5^1@2$7^3@2$6^2^1").
Proof.
  intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.
End FPX1.

(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            (* [comment removed for export] *)
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

(* [comment removed for export] *)
Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma callee_kept_no0 : ltac2:(zQ "80!o8!qc!lj7!ljb!mlf!lj1!lm1!lm6@1$3@3$5@1$1@1$0#5Kd@3$6@1$0#5ZKv$2@2$7@1$0#5Z@1$1@1$0#5$4").
Proof.
  unfold callee_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End FPX2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
