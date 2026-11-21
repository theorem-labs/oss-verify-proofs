(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/EhCut.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/EhCut.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhCut.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~04expr04EVar37Corelib7Numbers7BinNumsl11Z37Corelib4Init9Datatypesme3natme4bool46Stdlib5Arith8PeanoNat3Natp33eqb37Corelib4Init3Natr43add04ELit89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~t24RATPt23vGP3h5LinuxProcessSemantics5Riscv5Instrhhf7ALU_ADD04EAlume4listme4prodme4consme4pairme3nil06kentry04KImgme3appme3fstme3snd37Corelib5Lists7ListDefhp63map05KWord02SAt29IMG_WORDSt23litt27vCANARYt25vAUXVt24vRNDt24vUIDt24vX12t24vX16t24vX23t23vX6t27USP_OFFt23addt22vA05saddrt27CUR_OFF46Stdlib6ZArith6BinInt1Zij23addt22cb03KWrt2bfslots_fromt2bxslots_fromt24vHDRt24vP2Vt24sitet27s_fsizet24vSPF04KUnkt27s_savedt28saved_knt23vRAij23subt23ZLOt23ZHIme4truet2aLOCALS_OFFt22cvt27auxv_knt29cursor_knt28flags_knt28geomT_knt26hdr_knt26img_knt2cstepframe_knt28frame_knt28geomB_knt26cut1_Bt26cut1_Tt23uspt24vS10t24vS11t23vS5t23vS8t23vS909sym_stateme4None03SSR06sentryt22NXt27cut1_knt29cut1_regshp63seqt27CUT1_PCt25s_padt2h0P1_HANDLER_FOUNDij23eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ERU5EhCut3CUTjv37auxv_knjv36cut1_Tjv37cut1_kn" s.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT.
Definition AUXV_RSEQ : bool := true.
Definition auxv_kn : list kentry :=
  [ KWord (SA (lit 0) 1240720) 8 vAUXV
  ; KWord (SA vAUXV 0) 8 (lit 33)
  ; KUnk (SA vAUXV 8) (lit 8)
  ; KWord (SA vAUXV 16) 8 (lit 40)
  ; KWord (SA vAUXV 32) 8 (lit 41)
  ; KWord (SA vAUXV 48) 8 (lit 42)
  ; KWord (SA vAUXV 64) 8 (lit 43)
  ; KWord (SA vAUXV 80) 8 (lit 44)
  ; KWord (SA vAUXV 96) 8 (lit 45)
  ; KWord (SA vAUXV 112) 8 (lit 46)
  ; KWord (SA vAUXV 128) 8 (lit 47)
  ; KWord (SA vAUXV 144) 8 (lit 51)
  ; KWord (SA vAUXV 160) 8 (lit 16)
  ; KWord (SA vAUXV 168) 8 vX16
  ; KWord (SA vAUXV 176) 8 (lit 6)
  ; KWord (SA vAUXV 184) 8 vX6
  ; KWord (SA vAUXV 192) 8 (lit 17)
  ; KWord (SA vAUXV 200) 8 (lit 100)
  ; KWord (SA vAUXV 208) 8 (lit 3)
  ; KWord (SA vAUXV 216) 8 (lit 65600)
  ; KWord (SA vAUXV 224) 8 (lit 4)
  ; KWord (SA vAUXV 232) 8 (lit 56)
  ; KWord (SA vAUXV 240) 8 (lit 5)
  ; KWord (SA vAUXV 248) 8 (lit 10)
  ; KWord (SA vAUXV 256) 8 (lit 7)
  ; KWord (SA vAUXV 264) 8 (lit 0)
  ; KWord (SA vAUXV 272) 8 (lit 8)
  ; KWord (SA vAUXV 280) 8 (lit 0)
  ; KWord (SA vAUXV 288) 8 (lit 9)
  ; KWord (SA vAUXV 296) 8 (lit 290456)
  ; KWord (SA vAUXV 304) 8 (lit 11)
  ; KWord (SA vAUXV 312) 8 vUID
  ; KWord (SA vAUXV 320) 8 (lit 12)
  ; KWord (SA vAUXV 328) 8 vX12
  ; KWord (SA vAUXV 336) 8 (lit 13)
  ; KUnk (SA vAUXV 344) (lit 8)
  ; KWord (SA vAUXV 352) 8 (lit 14)
  ; KUnk (SA vAUXV 360) (lit 8)
  ; KWord (SA vAUXV 368) 8 (lit 23)
  ; KWord (SA vAUXV 376) 8 vX23
  ; KWord (SA vAUXV 384) 8 (lit 25)
  ; KWord (SA vAUXV 392) 8 vRND
  ; KWord (SA vAUXV 400) 8 (lit 31)
  ; KUnk (SA vAUXV 408) (lit 8) ]
  ++ (if AUXV_RSEQ then
        [ KWord (SA vAUXV 416) 8 (lit 27)
        ; KWord (SA vAUXV 424) 8 (lit 28)
        ; KWord (SA vAUXV 432) 8 (lit 28)
        ; KWord (SA vAUXV 440) 8 (lit 32)
        ; KWord (SA vAUXV 448) 8 (lit 0) ]
      else [ KWord (SA vAUXV 416) 8 (lit 0) ]).

(* [comment removed for export] *)
Definition cut1_T : ltac2:(zQ "30!oc!hl4!hn6>6phase2$0@1$1$2") := ltac2:(zQ "a0!ho4!hn6!oc!kid!iv4!jg0!jgb!jh6!jhf!ji8\6phase2$2@3$0$1@1$9^1@3$0$1@1$4^1@3$0$1@1$7^1@3$0$1$5@3$0$1$3@3$0$1$8@1$6^1").
Definition cut1_kn : ltac2:(zQ "40!oc!hl4!hn6!io5>6phase2$0>acatchframe$0>2st$3@1$1$2") := ltac2:(zQ "60!oc!ho4!hn6!jkd!kj8!io5\6phase2$0\acatchframe$0\2st$5@3$1$2@1$4^3@3$3^3^2^1").

(* [comment removed for export] *)
Definition cut1 : ltac2:(zQ "30!oc!jo5!io5>6phase2$0>acatchframe$0>2st$2$1") := ltac2:(zQ "a0!oc!jp0!hn0!jp7!ii1!jpc!jq4!kk2!jr3!io5\6phase2$0\acatchframe$0\2st$9@6$3+tnvk4@1$8^3@1$2$5@3$7^3^2^1$6@1$1$4").

(* [comment removed for export] *)
End CUT.
(* [comment removed for export] *)
