(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh81Z3h5LinuxProcessSemanticsfLinuxProcessSem5Statej59page_size46Stdlib6ZArith6BinInt1Zmf4landmf6modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~p7bround_up_pgj5fpage_round_up_Z" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : ltac2:(zQ "30!h4!j1!m3@3$0$1$2+hgg0"). Proof. reflexivity. Qed.

Lemma land_4095 : ltac2:(zQ "40!j1!h4!o7!oe>1x$0@3$1$0@2$2^1+vvf@2$3^1+hgg0").
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : ltac2:(zQ "40!j1!h4!t5!oe>1x$0>0@3$1$0@2$3^1+hgg0Z@3$1$0@1$2^2^2").
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : ltac2:(zQ "40!j1!h4!u3!t5>1x$0@3$1$0@1$3^1@1$2^1").
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
