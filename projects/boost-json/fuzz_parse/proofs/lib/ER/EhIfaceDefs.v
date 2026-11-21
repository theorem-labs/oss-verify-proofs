(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhIfaceDefs.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhIfaceDefs.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Step Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 EhCut.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhIfaceDefs.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lej62lthc2or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbEhIfaceDefs6EHDEFS~~~~~~ld9eh_static37Corelib4Init9Datatypesr14listr13nat04Npos35stdpp9bitvectorbdefinitionstc2bv37Corelib5Lists7ListDefve6repeattc7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hi83memr14consld2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ho58bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hsb5rsegsr13nilld5zeros36Stdlib5Lists4Listihe2Inho53le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ije2wzr16optionho52war16lengthhc2eqj63addj66of_natld7eh_idlej63powr14Noneve3mapld7PH_ADDRld6PH_ENTld6PH_NUMhc2exldceh_auxv_list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~iv84u64shi8aRAUXV_CELLr14prodr14pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jl64cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jpa8rw_cellsjl62C8r13fstr13sndve6ForallldcEH_IMG_WORDSjl62C4hi8aRSSP_GUARD" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module EHDEFS.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhIfaceDefs.EHDEFS.

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT.
Definition auxv_words_ok (m : mem) (av x16 x6 x11 x12 x23 rnd : Z) : Prop :=
  2^32 <= av /\ av + 464 <= 2^64
  /\ bytes_at rsegs m av (le8 (wz 33)) /\ (exists v, bytes_at rsegs m (av + 8) (le8 (wz v)))
  /\ bytes_at rsegs m (av + 16) (le8 (wz 40)) /\ bytes_at rsegs m (av + 32) (le8 (wz 41))
  /\ bytes_at rsegs m (av + 48) (le8 (wz 42)) /\ bytes_at rsegs m (av + 64) (le8 (wz 43))
  /\ bytes_at rsegs m (av + 80) (le8 (wz 44)) /\ bytes_at rsegs m (av + 96) (le8 (wz 45))
  /\ bytes_at rsegs m (av + 112) (le8 (wz 46)) /\ bytes_at rsegs m (av + 128) (le8 (wz 47))
  /\ bytes_at rsegs m (av + 144) (le8 (wz 51))
  /\ bytes_at rsegs m (av + 160) (le8 (wz 16)) /\ bytes_at rsegs m (av + 168) (le8 (wz x16))
  /\ bytes_at rsegs m (av + 176) (le8 (wz 6)) /\ bytes_at rsegs m (av + 184) (le8 (wz x6))
  /\ bytes_at rsegs m (av + 192) (le8 (wz 17)) /\ bytes_at rsegs m (av + 200) (le8 (wz 100))
  /\ bytes_at rsegs m (av + 208) (le8 (wz 3)) /\ bytes_at rsegs m (av + 216) (le8 (wz PH_ADDR))
  /\ bytes_at rsegs m (av + 224) (le8 (wz 4)) /\ bytes_at rsegs m (av + 232) (le8 (wz PH_ENT))
  /\ bytes_at rsegs m (av + 240) (le8 (wz 5)) /\ bytes_at rsegs m (av + 248) (le8 (wz PH_NUM))
  /\ bytes_at rsegs m (av + 256) (le8 (wz 7)) /\ bytes_at rsegs m (av + 264) (le8 (wz 0))
  /\ bytes_at rsegs m (av + 272) (le8 (wz 8)) /\ bytes_at rsegs m (av + 280) (le8 (wz 0))
  /\ bytes_at rsegs m (av + 288) (le8 (wz 9)) /\ bytes_at rsegs m (av + 296) (le8 (wz 291460))
  /\ bytes_at rsegs m (av + 304) (le8 (wz 11)) /\ bytes_at rsegs m (av + 312) (le8 (wz x11))
  /\ bytes_at rsegs m (av + 320) (le8 (wz 12)) /\ bytes_at rsegs m (av + 328) (le8 (wz x12))
  /\ bytes_at rsegs m (av + 336) (le8 (wz 13)) /\ (exists v, bytes_at rsegs m (av + 344) (le8 (wz v)))
  /\ bytes_at rsegs m (av + 352) (le8 (wz 14)) /\ (exists v, bytes_at rsegs m (av + 360) (le8 (wz v)))
  /\ bytes_at rsegs m (av + 368) (le8 (wz 23)) /\ bytes_at rsegs m (av + 376) (le8 (wz x23))
  /\ bytes_at rsegs m (av + 384) (le8 (wz 25)) /\ bytes_at rsegs m (av + 392) (le8 (wz rnd))
  /\ bytes_at rsegs m (av + 400) (le8 (wz 31)) /\ (exists v, bytes_at rsegs m (av + 408) (le8 (wz v)))
  /\ (if AUXV_RSEQ
      then bytes_at rsegs m (av + 416) (le8 (wz 27)) /\ bytes_at rsegs m (av + 424) (le8 (wz 28))
           /\ bytes_at rsegs m (av + 432) (le8 (wz 28)) /\ bytes_at rsegs m (av + 440) (le8 (wz 32))
           /\ bytes_at rsegs m (av + 448) (le8 (wz 0))
      else bytes_at rsegs m (av + 416) (le8 (wz 0))).
Definition eh_auxv_ok (m : mem) (B : Z) : Prop :=
  exists av x16 x6 x11 x12 x23 rnd : Z,
    bytes_at rsegs m RAUXV_CELL (le8 (wz av)) /\ auxv_words_ok m av x16 x6 x11 x12 x23 rnd
    /\ B <= av /\ av + 464 <= 2^64
    /\ (0 <= x16 /\ x16 < 2^64) /\ (0 <= x6 /\ x6 < 2^64) /\ (0 <= x11 /\ x11 < 2^64)
    /\ (0 <= x12 /\ x12 < 2^64) /\ (0 <= x23 /\ x23 < 2^64) /\ (0 <= rnd /\ rnd < 2^64).

(* [comment removed for export] *)
(* [comment removed for export] *)
End EHDEFS.
(* [comment removed for export] *)
