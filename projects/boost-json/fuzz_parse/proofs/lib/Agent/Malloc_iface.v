(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep MallocHINV MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jb4cellhc4cons04Nposjb2C135stdpp9bitvectorbdefinitionsp07Z_to_bvhc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~rd5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hga3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hl46PState37Corelib4Init5Logichpa3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hr56mstatehpa2exhpa2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~ig95asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocHINV~~~~~~il59HINV_from79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~iq5eagent_reservediq54mrep89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface3HCW~~~~~~jg16MEDTABjg1cmedtab_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jm48rw_cellshr55striphl46ps_brkhl44ps_m36Stdlib7SortingbPermutationjs6bPermutationrd8blk_addrrd8blk_size36Stdlib5Lists4Listkg72In46Stdlib6ZArith6BinInt1Zki03addki02leki02lthl44bptrhc4boolhr54cptrhc3fsthc3sndhc4andbhr58aptr_eqbki03eqbhc4negbrd6blk_idjg18bptr_eqb36Stdlib4Bool4Boolkq47Is_true25stdpp4baseks16filter25stdpp9decidablekt7bIs_true_dec35stdppblist_basics4listkv7blist_filter" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition AGP : Z := 0x1a800.          (* [comment removed for export] *)
         (* [comment removed for export] *)
     (* [comment removed for export] *)
  (* [comment removed for export] *)
    (* [comment removed for export] *)
   (* [comment removed for export] *)
     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MEDTAB : Z := 0x1a060.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition medtab_cells : ltac2:(zQ "20!j4!n7@1$0$1") := ltac2:(zQ "60!n7!ne!o5!ob!qd!r7@3$1$0@1$3@2$4@1$2#8+hc@3$1$0@1$3@2$4@1$2#8+h8@3$1$0@1$3@2$4@1$2#8+h4@3$1$0@1$3@2$4@1$2#8+i0@1$5$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HEAP : ltac2:(zQ "40!j4!hg2!hkd!hp0>1s$3>2LB@1$0$1>1m$2P") := ltac2:(zQ "h30!hqe!hg2!j4!hv3!hvd!ig3!ikc!ip8!iu7!iv9!hkd!jka!jl4!jpf!jqb!hp0!jr4!jre!ju2\1s$f\2LB@1$2$1\1m$a@2$4$3\2st$3@2$4@1$2$1\3LB0@1$2$1@2$0@3$h2$1^1^4@2$0@3$5$3@1$e^2@1$h1^5@2$0@2$9^2^3@2$0@5$7?4HSEC$8^2@1$h0^5^1@4$d$6^3$b$c").

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_block : ltac2:(zQ "30!j4!h9!hg2>2LB@1$0$2>1a$1P") := ltac2:(zQ "b0!hg2!hqe!jv1!j4!hvd!h9!jvc!kha!kj8!kjf!kk5\2LB@1$3$0\1a$5@2$4$0\1b$0@2$1@3$7$0^1^3@2$1@2$9@1$2^1^2@2$a^2@2$8@1$2^1@1$6^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)



(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
 (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bptr_eqb : ltac2:(zQ "20!kkb!kl3>1p$0>1q$0$1") := ltac2:(zQ "80!h9!kla!km2!km8!kkb!kme!kn5!ko1\1p$4\1q$4@2$5@2$6@3$2$1$0^2@3$2$1$0^1@2$7@3$3$1$0^2@3$3$1$0^1").
(* [comment removed for export] *)
Definition lb_remove : ltac2:(zQ "30!j4!hg2!kkb>1p$2>2LB@1$0$1@1$0$1") := ltac2:(zQ "a0!hg2!j4!ko8!kof!kp8!kkb!kr6!ksd!ku8!lgf\1p$5\2LB@1$1$0@6$7$0@1$1$0@1$9$0\1b$0@1$6@1$2@2$4@1$3^1^3\1x$0@1$8@1$2@2$4@1$3^1^3^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

End HCW.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
