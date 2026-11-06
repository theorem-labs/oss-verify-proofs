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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SymExec2 SymExec2Sound SymRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv03nat03nil37Corelib5Lists7ListDefma3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~o78sidecond04prod06option37Corelib4Init5Logictf2eqo76kentry04bool04pairo77scriptso79sym_statehe1Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi75mkCfg3h5LinuxProcessSemantics5Riscv7Preludehlc5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hob4mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hse8realizeso75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ihd7know_okihd7regs_okihd9scs_denotje7Z_to_bv04None04true3h5LinuxProcessSemanticsfLinuxProcessSem5Stateipb5Modelipb8m_haltedipb9m_vm_lazyhse4TSeto72SSo75carryo73envo74expro74s_pco76s_regso76sentryo78sym_execihd9mem_denoto74lres04Some05falseo7bknow_lookuptf3and37Corelib4Init5Peanojm62leo72SA06lengthtf2ex3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejp2dbytes_le_to_Zhob3rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive5Drive~~~~~~jt95kreado76adenoto76edenotihd4flat46Stdlib6ZArith6BinInt1Zkjd6of_nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsklfh0word_to_le_byteskjd3addhob6v_addikjd2lekjd2ltkjd3powtf1Ije2BVje4BvWfhob6regupdo74ridxo76sr_updma3mapma3seqhob4getr37Corelib4Init3Natlgd3addo74ELito74EVar46Stdlib5Arith8PeanoNat3Natlj43eqb36Stdlib5Lists4Listll67existsb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~ln4cexpr_vars_ltln4asr_vars_lto73Envln47vals_evll62In03apptf3notjm62ltjt99junk_valsjt9fsr_after_call_j3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypemh37Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition blobs_ev : ltac2:(zQ "40!h8!j7!lb!m0>2bl@1$0@1$0@1$2@1$1#8>0$3@1$0@1$2@1$1#8") := ltac2:(zQ "60!h8!j7!lb!m0!m5!o1\2bl@1$0@1$0@1$2@1$1#8\1n$3@4$5@1$0@1$2@1$1#8^1^2@1$4@1$2@1$1#8").
End FPX1.

Section Drive.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!h8!mk8@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rz_run : ltac2:(zQ "i72!j7!h8!lb!s6!t1!t7!v3!v8!hg1!m5!hg7!hgd!hh7!m0!hi3!hl3!ho2!hs6!ig9!ih5!im2!imd!in8!io5!iof!ip5!is9!it2!ite!iub!iv3!iv8!jg0!jg6!jgd!jh4!jhd!ji6!jj1&>0@1$2@1$0#k0@1$5@1$2@1$0#8&@2$4@1$2@1$0#k0@1$2@1$0#k0>4fuel$d>5stops@1$1$e>3scr$b>2pc$e>2sr@1$1$i1>2kn@1$1$7>2nx$d>3ss'$c>3scs@1$1$3>4scr'$b>3kn'@1$1$7>4scs2@1$1$3>3hs2@1$1$8>1E$i0>1M~0>3rom~0>1R@2$h0@1$0#5@1$2@1$0#k0>5model$ha>1T$hd>0@3$6@2$4@2$4$c@1$1$3$b@7$i5?4segs^h3$h9^h2^h1@5$he^h0^f@1$9$i4^e^d@1$9$3@4$a@2$4$c@1$1$3$b@4$a$c@1$1$3^c^b^a>0@3$6@2$4@2$4@1$1$7@1$1$3@1$1$8@3$hf@1$h3^d^f@1$9$8@4$a@2$4@1$1$7@1$1$3@1$1$8@4$a@1$1$7@1$1$3^a^9^8>0@3$h5^8^h1^5>0@4$h4?4segs^9^8^h1>0@4$h6?4segs^9^a^f>0@4$h6?4segs^a^b^d>0@3$6@1$5@1$2@1$0#k0@1$hb^8@1$h8@1$2@1$0#k0>0@3$6@1$1~1@1$hc^9@1$9~1>0>2R'@2$h0@1$0#5@1$2@1$0#k0>2M'~0>0@3$h5^h0@1$i3^h6^2>0@4$h4?4segs^h1^2^h4>0@3$6~0^3@3$i6^h2^h1@1$h3^h8@4$h2?4segs?2SC@2$f@5$h1?2fx^5@2$h7@1$0#k0@1$i2^h9^4^h1^f^e@4$h2?4segs?2SC@2$f@5$h1?2fx^c@2$h7@1$0#k0^h9^e^d^b^a").
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  ndestruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kread : ltac2:(zQ "60!jg6!h8!m0!t7!hi3!v8>2kn@1$1$5>1b$0>1k$4>1n$2@1$3$0") := ltac2:(zQ "e0!h8!jg6!s6!iof!hg1!m5!t7!jje!jk5!jkb!m0!hi3!v8!jl2\2kn@1$0$c\1b$1\1k$b\1n$aM7\1x$7@1$6$1@8$d?4segs^4^3^2^1$9@1$5$4@1$5$2\1v$1\3scs@1$0$2\5hints@1$0$4M0\3scs@1$0$2@1$6$1^2@2$8$1^3\1s$2\1l@1$0$2@1$3$1\3scs@1$0$2\5hints@1$0$4@1$3$1@1$3$1").

Lemma kread_sound : ltac2:(zQ "h90!j7!lb!h8!v3!jg6!t7!jk5!m0!jm0!jna!jo0!jo5!jod!hi3!js1!jt2!kha!ki3!kic!jg0!v8!kj5!im2!kl5!io5>1E$h3>1M>0@1$1@1$0#k0@1$5@1$1@1$0#8>2kn@1$2$h4>1b$4>1k$d>1n$7>1v$4>0@4$h6?4segs^7^6^5>0@3$3@1$5$4@4$h0^6^5^4^3@2$6$4^2>0@2$9N1^4>0@2$9^5N8>0@3$h5^b@2$a^8^7@1$h7^6@2$c@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@2$8@3$3@1$5@1$2@1$1@1$0#8@4$f?4segs^c@2$h1^d@2$a^a^9^8@2$6@1$2@1$1@1$0#8^1@2$8@3$3$7@2$b@1$1@1$0#8^1^8@3$3@1$1@1$0#k0@2$h8@1$0#k0@1$e^1@2$h2^d^7").
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
  pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
  destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection Hr as ->.
  ndestruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

Lemma word_to_le_bytes_of_lez : ltac2:(zQ "a0!j7!lb!h8!m0!v3!jo5!jna!js1!kp6!io5>1n$3>2bs@1$2@1$1@1$0#8>0@3$4$3@2$5@1$1@1$0#8^1^2>0@2$6^3N8@3$4@1$2@1$1@1$0#8@2$8^4@2$9@1$0#k0@1$7^3^3").
Proof.
  intros n bs Hl Hn. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma kread_rdn : ltac2:(zQ "h50!j7!jg6!lb!h8!t7!jk5!v3!jna!jo0!m0!hi3!kp6!jt2!kha!ki3!kic!jg0!v8!kj5!im2!kl5>1E$h0>1M>0@1$2@1$0#k0@1$4@1$2@1$0#8>2kn@1$3$h1>1b$1>1k$a>1n$9>1v$1>0@4$h3?4segs^7^6^5>0@3$6@1$4$1@4$d^6^5^4^3@2$5$1^2>0@2$7N1^4>0@2$7^5N8>0@3$h2^b@2$8^8^7@1$h4^6@3$6@1$4@1$3@1$2@1$0#8@4$c?4segs^b@2$e^c@2$8^9^8^7@2$5@1$3@1$2@1$0#8@2$b^7@2$f^c^6").
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
  ndestruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
  rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_pc4 : ltac2:(zQ "a0!j7!kqb!io5!v3!hi3!kr2!krc!ks2!ks8!lb>2pc$4>0@2$6Z^1>0@2$7@2$1^2+4@2$8+2+k0@3$3@1$9@1$0#k0@2$5@2$2@1$0#k0^3+4@2$2@1$0#k0@2$1^3+4").
Proof. intros pc H0 H1. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma regs_set_a0 : ltac2:(zQ "f1!j7!lb!ksf!jg6!imd!kt3!kt8!h8!v3!ho2!ktf!kic!jg0!ku9!kv0&@3$5@1$0#5+aKv$2@2$6@1$0#5+a>1E$c>2sr@1$7$3>1R@2$9@1$0#5@1$1@1$0#k0>1v@1$1@1$0#k0>1e$3>0@3$4^5^4^3>0@3$8@1$1@1$0#k0@2$b^6^2^3@3$4^7@3$e^6@1$d~0^3@3$a^5~0^4").
Proof. intros. apply regs_ok_set; [assumption | discriminate | assumption]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition junk_vals : ltac2:(zQ "40!j7!lb!h8!ho2>2R'@2$3@1$0#5@1$1@1$0#k0@1$2@1$1@1$0#k0") := ltac2:(zQ "90!j7!m0!lb!kv9!kvf!ho2!lg5!kl5!io5\2R'@2$5@1$0#5@1$2@1$0#k0@4$3$1@1$2@1$0#k0\1i$1@2$6^2@2$8@1$0#5@1$7^1@2$4N0Ni0").

Definition sr_after_call_j : ltac2:(zQ "30!h8!m0!jg6>2sr@1$0$2>4kept@1$0$1>5jbase$1@1$0$2") := ltac2:(zQ "c0!m0!jg6!hg1!h8!lhf!kv9!o1!kvf!li6!lid!lkf!lm9\2sr@1$3$1\4kept@1$3$0\5jbase$0@4$5$0$1\1i$0M2\0$2$1@3$b$0@1$a^1^3@4$6$1^1^4@1$8Z@1$9@2$4^2^1@2$7N0Ni0").

Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
  nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
  intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
  cbn [seq map]. destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
  nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

Lemma sr_vars_lt_nth : ltac2:(zQ "a0!hg1!m0!ip5!v3!jg6!h8!o1!li6!lqd!lrd>1b$1>2sr@1$5$4>1n$1>0@3$3$0@2$9^3^2$2@3$3$0@2$8^4@4$6$4^2^3@1$7Z$2").
Proof.
  intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

Lemma regs_after_call : ltac2:(zQ "h80!j7!lb!m0!h8!jo5!v3!ho2!lg5!lsb!imd!lt1!ltc!kl5!io5!lu2!hg1!ip5!jm0!lu7!lud!lv3!mg0!jg6!lrd>4vals@1$3@1$1@1$0#k0>3ebs>0$2@1$3@1$1@1$0#8>2sr@1$3$h6>1R@2$6@1$0#5@1$1@1$0#k0>2R'@2$6@1$0#5@1$1@1$0#k0>4kept@1$3$2>0@3$5$f@2$h7@2$4@1$1@1$0#k0^6^4$h0>0@3$9@2$8@1$a^7^6^5^4>0>1i$2>0@3$b$2^1^4@2$h1@2$h3^2Ni0@3$5@1$1@1$0#k0@2$7^6@2$d@1$0#5@1$c^2@2$7^7@2$d@1$0#5@1$c^2>0@1$h2@3$b$2N0^4@3$9@2$8@1$a@3$e@1$1@1$0#k0^a@1$h4^6^9@3$h5^8^5@2$4@1$1@1$0#k0^a^6").
Proof.
  intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
  pose proof (ridx_range r) as Hr.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
    destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
    + apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
      destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
      pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
      eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
    + cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
      replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
      unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

End Drive.
(* [comment removed for export] *)
