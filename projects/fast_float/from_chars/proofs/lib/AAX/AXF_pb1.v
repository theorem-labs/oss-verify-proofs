(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_AD := EVar 32.
Definition e_SZ := EVar 33.
Definition e_S0 := EVar 34.
Definition e_S1 := EVar 35.
Definition e_S2 := EVar 36.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pb1 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 515004)) 10 (e_AD)) 19 (e_SZ)) 20 (e_AD)).
Definition kn_pb1 : list kentry :=
  [ KRange e_AD 17594333495296 (2^47-2^20);
    KAlign e_AD 4096;
    KRange e_SZ 4096 (2^20);
    KAlign e_SZ 4096;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 935452) 1 (ELit 1);
    KWord (SA (ELit 0) 904208) 8 (ELit 937400);
    KWord (SA (ELit 0) 937400) 8 (ELit 2147450880);
    KWord (SA (ELit 0) 904216) 8 (ELit 940712);
    KWord (SA (ELit 0) 940712) 8 (ELit 0);
    KWord (SA (ELit 0) 904224) 8 (ELit 940720);
    KWord (SA (ELit 0) 940720) 8 (ELit 0);
    KWord (SA (ELit 0) 904232) 8 (ELit 940704);
    KWord (SA (ELit 0) 940704) 8 (ELit 140737488355327);
    KWord (SA (ELit 0) 904240) 8 (ELit 912208);
    KWord (SA (ELit 0) 912208) 8 (ELit 864392);
    KWord (SA (EVar 2) 24) 8 (ELit 280928);
    KWord (SA (EVar 2) 16) 8 e_S0;
    KWord (SA (EVar 2) 8) 8 e_S1;
    KWord (SA (EVar 2) 0) 8 e_S2;
    KWr (SA (EVar 2) 0) (ELit 32);
    KWr STK (ELit 1024) ].
Definition scr_pb1 : scripts := SCR [] [] [].
Definition ss_pb1 := SS 0x75a54 sr_pb1 [] kn_pb1 37.
Definition RUN_pb1 := sym_exec SEGS 200 true [0xd3088] scr_pb1 ss_pb1 [].

Definition scr_ppb1 : scripts := SCR [] [] [].
Definition RES_ppb1 := Eval vm_compute in sym_exec SEGS 200 true [0xd3088] scr_ppb1 ss_pb1 [].
Lemma RES_ppb1_ok : sym_exec SEGS 200 true [0xd3088] scr_ppb1 (SS 0x75a54 sr_pb1 [] kn_pb1 37) [] = RES_ppb1.
Proof. vm_compute. reflexivity. Qed.
