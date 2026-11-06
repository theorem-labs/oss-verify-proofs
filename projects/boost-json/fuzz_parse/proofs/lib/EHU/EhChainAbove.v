(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJChainAbove.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~05frame37Corelib4Init9Datatypeskb4list89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhIface3EHI~~~~~~ma9chain_okF08chain_sp05fr_sp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~s93mem36Stdlib5Lists4Listhha2In46Stdlib6ZArith6BinInt1Zhj32le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUcBJChainAbove~~~~~~hl1eeh_chain_abovema3EHK03hmf" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module EHA.
Section S.
  Context {HCEIL : HeapCeil}.

  Lemma chain_okF_above : ltac2:(zQ "80!k4!m3!qc!r8!s2!hh4!hid!hkb>1G@1$1$0>1m$5>1f$0>0@2$2^3^2>0@3$6$0^2^4@2$7@1$3^5@1$4^3").
  Proof.
    induction G as [|h G IH]; intros m f HC Hin; [destruct Hin|].
    cbn [chain_sp]. destruct Hin as [<-|Hin]; [lia|].
    destruct G as [|g G']; [destruct Hin|].
    ndestruct HC as (HG & _ & _ & Hsz & _).
    pose proof (IH m f HG Hin) as IHf. cbn [chain_sp] in IHf.
    pose proof (EHI.fsize_cnt_ok (fr_fn h)) as (B1 & _). lia.
  Qed.

  Theorem L_chain_above : ltac2:(zQ "30!hp4!hq6!hqc>2HM$2@1$0@1$1^1").
  Proof. intros HM G m f HC Hin. exact (chain_okF_above G m f HC Hin). Qed.
End S.
End EHA.
