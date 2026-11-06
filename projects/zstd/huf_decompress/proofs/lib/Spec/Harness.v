(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require FseNCount HufHarness.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Harness () := "I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec:HufHarnessBhuf_dt_bytes_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec:HufHarness>huf_dbuf_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec7Harness8BUFF_MAXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3add".
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition PRODUCER_SIZE : Z := 16.
(* [comment removed for export] *)
Definition BUFF_MAX : Z := HufHarness.DBUF_MAX.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dt_size (payload : list Z) : Z := HufHarness.huf_dt_bytes payload.
Definition WKSP_SIZE : Z := HufHarness.HUF_WORKSPACE_SIZE.     (* [comment removed for export] *)
Definition dbuf_size (payload : list Z) : Z := HufHarness.huf_dbuf payload.

Lemma dt_size_range : forall payload, zlength payload <= 2^26 -> 12 <= dt_size payload <= 16388.
Proof.
ltac2:(KReplay.run1 (kr_t_Harness ()) [] "h01Hh17payloadp;1p;2g0000j1:Tg000Pj29Tg001Hj10Tg001mj12Tg002Kj14Tg0030j28Tg003Mj23Tg003ij27Tg0050j16Tg005ij25Tf0R0#0#0p=1g006DR1#:1910g006bR1#0R2#2%41#0R1#4#0#2'8'3f1R3/70%01#2%63R3'3%12#1#1#1#1#4#1#2,33'5eW0W1o"). Qed.
Lemma WKSP_SIZE_val : WKSP_SIZE = 8704.
Proof.
ltac2:(KReplay.run1 (kr_t_Harness ()) [] "p;1p;2g001Hj11Tg002Kj13Tg001mj12Tg007Gj24Tf0#1#1p=0g006Dg006b#1#0#3#1#0#0#0#0#2'4o"). Qed.
Lemma dbuf_size_range : forall payload, zlength payload <= 2^26 -> 0 <= dbuf_size payload <= BUFF_MAX.
Proof.
ltac2:(KReplay.run1 (kr_t_Harness ()) [] "h01Hh17payloadp;1p;2g0000j19Tg000Pj28Tg001Hj10Tg001mj12Tg002Kj13Tg0030j27Tg003Mj21Tg007aj24Tg008dj15Tg005ij26Tg006DR0#9f0R1,80g006bR0#0#2%30#0#3#0#2'7'1f1R0/41g009_%50R0'1g00:=,10'6eW0W1o"). Qed.
Lemma BUFF_MAX_val : BUFF_MAX = 2^29 + 500.
Proof.
ltac2:(KReplay.run1 (kr_t_Harness ()) [] "p;1p;2g001Hj11Tg001mj12Tg002Kj10Tg0030j23Tg00;7j25Tg007Gj24Tg006Dg006bR0#1#2%00#0R0#1#0#2'3%00#0#1#0#1#1#2'5'4o"). Qed.

Section Harness.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).      (* [comment removed for export] *)
Variable raw_free : ptr -> M St unit.              (* [comment removed for export] *)
Variable new_handler : M St Empty_set.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fuzz_malloc (size : Z) : M St (option ptr) :=
  if 0 <? size then
    r <- raw_malloc size ;;
    match r with
    | Some p => mret (Some p)
    | None => e <- new_handler ;; match (e : Empty_set) with end
    end
  else mret None.

(* [comment removed for export] *)
Definition free_opt (p : option ptr) : M St unit :=
  match p with Some q => raw_free q | None => mret tt end.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z :=
  producer <- fuzz_malloc PRODUCER_SIZE ;;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  dt <- fuzz_malloc (dt_size data) ;;                (* [comment removed for export] *)
  wksp <- fuzz_malloc WKSP_SIZE ;;                   (* [comment removed for export] *)
  dBuf <- fuzz_malloc (dbuf_size data) ;;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  free_opt dt ;;;                                    (* [comment removed for export] *)
  free_opt wksp ;;;                                  (* [comment removed for export] *)
  free_opt dBuf ;;;                                  (* [comment removed for export] *)
  free_opt producer ;;;                              (* [comment removed for export] *)
  mret 0.

End Harness.
