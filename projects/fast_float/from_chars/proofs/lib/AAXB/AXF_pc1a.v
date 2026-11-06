(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_AD := EVar 32.
Definition e_SZ := EVar 33.
Definition e_S0 := EVar 34.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pc1a := (sr_upd (sr_upd sr_id 1 (ELit 514992)) 10 (e_AD)).
Definition kn_pc1a : list kentry :=
  [ KRange e_AD 17594333495296 (2^47-2^20);
    KAlign e_AD 4096;
    KRange e_SZ 4096 (2^20);
    KAlign e_SZ 4096;
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 941788) 1 (ELit 1);
    KWord (SA (ELit 0) 910480) 8 (ELit 943736);
    KWord (SA (ELit 0) 943736) 8 (ELit 2147450880);
    KWord (SA (ELit 0) 910488) 8 (ELit 947048);
    KWord (SA (ELit 0) 947048) 8 (ELit 0);
    KWord (SA (ELit 0) 910496) 8 (ELit 947056);
    KWord (SA (ELit 0) 947056) 8 (ELit 0);
    KWord (SA (ELit 0) 910504) 8 (ELit 947040);
    KWord (SA (ELit 0) 947040) 8 (ELit 140737488355327);
    KWord (SA (ELit 0) 910512) 8 (ELit 918480);
    KWord (SA (ELit 0) 918480) 8 (ELit 870660);
    KWord (SA (EVar 2) 24) 8 (ELit 272576);
    KWord (SA (EVar 2) 16) 8 e_S0;
    KWord (SA (EVar 2) 8) 8 e_AD;
    KWord (SA (EVar 2) 0) 8 e_SZ;
    KWr (SA (EVar 2) 0) (ELit 32);
    KWr STK (ELit 1024) ].
Definition scr_pc1a : scripts := SCR [] [] [].
Definition ss_pc1a := SS 0x75a48 sr_pc1a [] kn_pc1a 35.
Definition RUN_pc1a := sym_exec SEGS 200 true [0xd4904] scr_pc1a ss_pc1a [].

Definition scr_ppc1a : scripts := SCR [] [] [].
Definition RES_ppc1a := Eval vm_compute in sym_exec SEGS 200 true [0xd4904] scr_ppc1a ss_pc1a [].
Lemma RES_ppc1a_ok : sym_exec SEGS 200 true [0xd4904] scr_ppc1a (SS 0x75a48 sr_pc1a [] kn_pc1a 35) [] = RES_ppc1a.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
