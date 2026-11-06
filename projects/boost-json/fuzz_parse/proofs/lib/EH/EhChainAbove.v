(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJFrame HeapMF_iface BJChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import EhIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~05frame37Corelib4Init9Datatypesk94list08chain_sp05fr_sp89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhIface3EHI~~~~~~n99chain_okF79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~s63mem36Stdlib5Lists4Listhh62In46Stdlib6ZArith6BinInt1Zhif2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcBJChainAbove~~~~~~hkdeeh_chain_above03hmfn93EHK" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module EHA.
Section S.
  Context {HCEIL : HeapCeil}.

  Lemma chain_okF_above : ltac2:(zQ "80!k2!m1!m8!n2!ra!hh0!hi9!hk7>1G@1$1$0>1m$5>1f$0>0@2$4^3^2>0@3$6$0^2^4@2$7@1$2^5@1$3^3").
  Proof.
    induction G as [|h G IH]; intros m f HC Hin; [destruct Hin|].
    cbn [chain_sp]. destruct Hin as [<-|Hin]; [lia|].
    destruct G as [|g G']; [destruct Hin|].
    ndestruct HC as (HG & _ & _ & Hsz & _).
    pose proof (IH m f HG Hin) as IHf. cbn [chain_sp] in IHf.
    pose proof (EHI.fsize_cnt_ok (fr_fn h)) as (B1 & _). lia.
  Qed.

  Theorem L_chain_above : ltac2:(zQ "30!hof!hq1!hq6>2HM$1@1$0@1$2^1").
  Proof. intros HM G m f HC Hin. exact (chain_okF_above G m f HC Hin). Qed.
End S.
End EHA.
