(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhCut.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhCut.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhCut.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~04expr04EVar37Corelib7Numbers7BinNumsl11Z37Corelib4Init9Datatypesme3natme4bool46Stdlib5Arith8PeanoNat3Natp33eqb37Corelib4Init3Natr43add89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~sc4RATPsc3vGP04ELit3h5LinuxProcessSemantics5Riscv5Instrhhe7ALU_ADD04EAlume4listme4prodme4consme4pairme3nil06kentry04KImgme3appme3fstme3snd37Corelib5Lists7ListDefhp53mapsc9IMG_WORDS05KWord02SAsc3litsc7vCANARYsc5vAUXVsc4vRNDsc4vUIDsc4vX12sc4vX16sc4vX23sc3vX6sc7USP_OFFsc3addsc2vA05saddrsc7CUR_OFF46Stdlib6ZArith6BinInt1Zij13addsc2cbscbfslots_fromscbxslots_from03KWrsc4vHDRsc4vP2Vsc4sitesc7s_fsizesc7s_savedsc8saved_knsc3vRAsc4vSPFij13subsc3ZLOsc3ZHIme4truescaLOCALS_OFFsc2cvsc7auxv_knsc9cursor_knsc8flags_knsc8geomT_knsc6hdr_knsc6img_knsccstepframe_knsc8frame_knsc8geomB_knsc6cut1_Bsc6cut1_Tsc3uspsc4vS10sc4vS11sc3vS5sc3vS8sc3vS909sym_stateme4Nonesc2NXsc7cut1_knsc9cut1_regs03SSR06sentryhp53seqsc7CUT1_PCsc5s_padsch0P1_HANDLER_FOUNDij13eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2ER5EhCut3CUTjuc7auxv_knjuc6cut1_Tjuc7cut1_kn" s.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT.
Definition AUXV_RSEQ : bool := true.
Definition auxv_kn : list kentry :=
  [ KWord (SA (lit 0) 1227088) 8 vAUXV
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
  ; KWord (SA vAUXV 296) 8 (lit 291460)
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
Definition cut1_T : ltac2:(zQ "30!oc!hl3!hn5>6phase2$0@1$1$2") := ltac2:(zQ "a0!ho3!hn5!oc!ki5!iud!iv9!jg4!jgf!jh8!ji1\6phase2$2@3$0$1@1$9^1@3$0$1@1$4^1@3$0$1@1$7^1@3$0$1$5@3$0$1$3@3$0$1$8@1$6^1").
Definition cut1_kn : ltac2:(zQ "40!oc!hl3!io4!hn5>6phase2$0>acatchframe$0>2st$2@1$1$3") := ltac2:(zQ "60!oc!ho3!jk6!kj0!io4!hn5\6phase2$0\acatchframe$0\2st$4@3$1$5@1$3^3@3$2^3^2^1").

(* [comment removed for export] *)
Definition cut1 : ltac2:(zQ "30!oc!io4!jne>6phase2$0>acatchframe$0>2st$1$2") := ltac2:(zQ "a0!oc!jo9!hmf!jp0!kja!jpf!io4!jqb!ii0!jr0\6phase2$0\acatchframe$0\2st$6@6$7+tkqpc@1$5^3@1$2$9@3$4^3^2^1$3@1$1$8").

(* [comment removed for export] *)
End CUT.
(* [comment removed for export] *)
