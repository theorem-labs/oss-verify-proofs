(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_LargeAlloc1 AS_Refill1 AllocTacX AllocPerfKit.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z46Stdlib6ZArith6BinInt1Zi23addi22le35stdpp9bitvectorbdefinitionsk52bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAS_Refill1~~~~~~m74RENVk5bbv_unsigned37Corelib4Init9Datatypesrc4listrc6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~u45asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAllocPerfKit~~~~~~hi77out_img79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hn43mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hr9ddisjoint_fromhr93ivlhr95munchhr95wmono" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma rrenv_transport_img : ltac2:(zQ "h00!h9!hf!ja!k0!m2!q7!qe!t4!tb!hhf!hm9!hr2!hv5!ig6!igd!ih6>2tp@1$4@1$0#k0>3TSD$1>3CTX$1>2TH$1>2sb$1>3ARI$1>1m$b>2m'>0@1$4@1$0#k0@1$8@1$4@1$0#8>1W@1$7$d>0@7$5^9^8^7^6^5^4^3>0@3$e^2^4^3>0@3$f$9^5^4>0@1$a^4>0@2$3+hggg0@2$2@2$6@1$0#k0^d-l8>0@2$3@2$2@2$2@2$6@1$0#k0^e-l8+8+nhjgg0>0@2$3+hggg0^e>0@2$3@2$2^f+8+nhjgg0>0@3$c^9@2$2^f+p8+8@7$5^h2^h1^h0^f^e^d^b").
  Proof.
    intros tp TSD CTX TH sb ARI m m' W E MU WM HW T1 T2 D1 D2 DC.
    apply (AS_Refill1.renv_transport tp TSD CTX TH sb ARI m m' W E MU WM); try exact DC; apply (out_img_disjoint W _ _ HW); lia.
  Qed.
End HCW.

(* [comment removed for export] *)
Ltac rrenv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AS_Refill1.RENV ?tp ?TSD ?CTX ?TH ?sb ?ARI m =>
      assert (E' : AS_Refill1.RENV tp TSD CTX TH sb ARI m');
      [ apply (rrenv_transport_img tp TSD CTX TH sb ARI m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.
