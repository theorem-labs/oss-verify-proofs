(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr06mstate37Corelib4Init9Datatypeskc4Some08upd_metakc6option0am_set_next0am_set_prev0cget_meta_rec06m_prev04meta04optr05lhead08set_head79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W18~~~~~~s9aas_fm_links9cas_fm_single08get_head37Corelib4Init5Logichj12eq01Mkc4Nones9bas_queue_st06m_next05queue05LFree05meta008put_metas98as_fm_st09free_meta37Corelib7Numbers7BinNumshq01Zkc4listkc4pairkc4prodhj13andhj13not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hu13ivlhu17outside36Stdlib5Lists4Listiif2In46Stdlib6ZArith6BinInt1Zik82leik82lt" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_fm_link : ltac2:(zQ "20!je!k4>3st0$1>1g$0>4head$0$1") := ltac2:(zQ "b0!je!k4!m4!mb!n5!ne!oa!p6!q4!qc!r2\3st0$1\1g$0\4head$0=5hprev$a@1$8@2$7^3^1=3st1$1@3$3^3\1r$9@2$6^2@2$5@2$2$0^3^1^4=3st2$1M4\5hprev@1$4$0$1^2\2pv$0@3$3^1@1$5@2$2$0^5^2^1@3$3^4@1$6@2$2$0^5^1").

Definition as_fm_single : ltac2:(zQ "30!k4!je!r8>3st0$0>1h$2>1g$1$0") := ltac2:(zQ "90!je!m4!r8!ne!oa!qc!k4!rf!mb\3st0$6\1h$2\1g$0@3$7^2@2$1$0^1@3$8^1\1r$5@2$4@2$1$0^2@2$3@2$1$0^2^1^3").

Definition as_queue_st : ltac2:(zQ "30!k4!je!r8>1h$2>1g$1>3st0$0$0") := ltac2:(zQ "70!je!n5!k4!hgb!hh8!hi7!r8\1h$6\1g$0\3st0$2M1\1x@1$1$0$2@2$5^1^3\4head$0@3$3^2^3^1@3$4^1^3^2").

Lemma as_queue_eq : ltac2:(zQ "c0!hk5!hkb!je!hke!p6!k4!r2!hl5!r8!hm3!q4!hmb>1RT>1h$8>1g$2>3st0$5>1k>0$5@1$1^5>4bail@1$1^5>0@3$0$6@1$9@2$4^3^4@1$3$2>0@3$0$6@1$a@2$4^4^5@1$3$2@3$0@1$1^8@6$b^8^7^6^5^4^3@1^4@3$7^7^6^5").
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st : ltac2:(zQ "20!k4!je>2st$0>1g$1$0") := ltac2:(zQ "60!hl5!hn2!je!hn9!k4!ho0\2st$4\1g$2@3$0$1^1@3$5^1$3^2").

Lemma as_free_meta_eq : ltac2:(zQ "60!hkb!k4!hk5!hoa!je!hp5>1RT>2st$1>1g$4>1k>0$1@1$0^4>4bail@1$0^4@3$2@1$0^5@5$5^5^3^4^2^1@1^2@2$3^4^3").
Proof.
  intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma outside_In : ltac2:(zQ "b0!hr9!hre!hs5!hsc!ht3!hta!ihd!ii4!ik2!im0!im6>1W@1$1$6>1x$0>2lo$0>2hi$0>0@2$7^4^3>0@3$8@2$3$0$0@4$2$0$0^3^2^5@1$5@2$4@2$9^4^5@2$a^5^3").
Proof. intros W x lo hi.
  induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
  destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

End FAILM.
(* [comment removed for export] *)
