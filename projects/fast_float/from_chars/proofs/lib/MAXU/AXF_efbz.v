(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.

Module AXF_efb.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_n := EVar 34.
Definition e_mem := EVar 35.
Definition e_sz := EVar 36.
Definition e_st := EVar 37.
Definition e_off := EVar 38.
Definition STRIDE := EMd M_MUL (ELit 16) e_sz.
Definition P := EAlu ALU_ADD e_st (EMd M_MUL (ELit 16) e_off).
Definition sr_efb := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G)) 11 (e_idx)) 12 (e_n)) 14 (STRIDE)) 15 (e_st)) 16 (e_mem)) 17 (e_off)).
Definition kn_efb : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_n 1 (2^26);
    KRange e_mem 1 (2^63-1);
    KRange e_sz 1 (2^23);
    KRange e_st 17 (2^63-1);
    KRange e_off 0 255;
    KWord (SA e_G 16) 8 e_mem;
    KWr (SA e_st (-4)) (ELit 4);
    KDisj (SA e_G 16) (ELit 8) (SA e_st (-4)) (ELit 4) ].
Definition scr_efb : scripts := SCR [] [] [].
Definition ss_efb := SS 0x54a04 sr_efb [] kn_efb 39.
Definition RUN_efb := sym_exec SEGS 200 true [] scr_efb ss_efb [].

Definition scr_efb_TT : scripts := SCR [true; true] [] [].
Definition RES_efb_TT := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_TT ss_efb [].
Lemma RES_efb_TT_ok : sym_exec SEGS 200 true [] scr_efb_TT (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_TT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efb_FT : scripts := SCR [false; true] [] [].
Definition RES_efb_FT := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_FT ss_efb [].
Lemma RES_efb_FT_ok : sym_exec SEGS 200 true [] scr_efb_FT (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_FT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efb_TFT : scripts := SCR [true; false; true] [] [].
Definition RES_efb_TFT := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_TFT ss_efb [].
Lemma RES_efb_TFT_ok : sym_exec SEGS 200 true [] scr_efb_TFT (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_TFT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efb_TFF : scripts := SCR [true; false; false] [] [].
Definition RES_efb_TFF := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_TFF ss_efb [].
Lemma RES_efb_TFF_ok : sym_exec SEGS 200 true [] scr_efb_TFF (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_TFF.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efb_FFT : scripts := SCR [false; false; true] [] [].
Definition RES_efb_FFT := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_FFT ss_efb [].
Lemma RES_efb_FFT_ok : sym_exec SEGS 200 true [] scr_efb_FFT (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_FFT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efb_FFF : scripts := SCR [false; false; false] [] [].
Definition RES_efb_FFF := Eval vm_compute in sym_exec SEGS 200 true [] scr_efb_FFF ss_efb [].
Lemma RES_efb_FFF_ok : sym_exec SEGS 200 true [] scr_efb_FFF (SS 0x54a04 sr_efb [] kn_efb 39) [] = RES_efb_FFF.
Proof. vm_compute. reflexivity. Qed.
End AXF_efb.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_efb.
Import ListNotations AX2 AX2S.

Module AXF_mam1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition STK := SA (EVar 2) (-1024).
Definition sr_mam1 := (sr_upd sr_id 10 (e_n)).
Definition kn_mam1 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_n 157 131051 ].
Definition scr_mam1 : scripts := SCR [] [] [].
Definition ss_mam1 := SS 0x530c8 sr_mam1 [] kn_mam1 33.
Definition RUN_mam1 := sym_exec SEGS 100 true [0x53e2c] scr_mam1 ss_mam1 [].

Definition RES_mam1 := Eval vm_compute in RUN_mam1.
Lemma RES_mam1_ok : sym_exec SEGS 100 true [0x53e2c] scr_mam1 (SS 0x530c8 sr_mam1 [] kn_mam1 33) [] = RES_mam1.
Proof. vm_compute. reflexivity. Qed.
End AXF_mam1.

Module AXF_mc0a.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_u := EVar 32.
Definition sr_mc0a := (sr_upd (sr_upd sr_id 19 (ELit 98952)) 20 (e_u)).
Definition kn_mc0a : list kentry :=
  [ KRange e_u 10 8190 ].
Definition scr_mc0a : scripts := SCR [] [] [].
Definition ss_mc0a := SS 0x53e2c sr_mc0a [] kn_mc0a 33.
Definition RUN_mc0a := sym_exec SEGS 100 true [0x53e50] scr_mc0a ss_mc0a [].

Definition RES_mc0a := Eval vm_compute in RUN_mc0a.
Lemma RES_mc0a_ok : sym_exec SEGS 100 true [0x53e50] scr_mc0a (SS 0x53e2c sr_mc0a [] kn_mc0a 33) [] = RES_mc0a.
Proof. vm_compute. reflexivity. Qed.
End AXF_mc0a.

Module AXF_mc0b.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_y := EVar 32.
Definition sr_mc0b := (sr_upd (sr_upd sr_id 10 (e_y)) 11 (ELit 125613361)).
Definition kn_mc0b : list kentry :=
  [ KRange e_y 0 4294967295 ].
Definition scr_mc0b : scripts := SCR [] [] [].
Definition ss_mc0b := SS 0x53e50 sr_mc0b [] kn_mc0b 33.
Definition RUN_mc0b := sym_exec SEGS 100 true [0x53e6c] scr_mc0b ss_mc0b [].

Definition RES_mc0b := Eval vm_compute in RUN_mc0b.
Lemma RES_mc0b_ok : sym_exec SEGS 100 true [0x53e6c] scr_mc0b (SS 0x53e50 sr_mc0b [] kn_mc0b 33) [] = RES_mc0b.
Proof. vm_compute. reflexivity. Qed.
End AXF_mc0b.

Module AXF_mc1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_s := EVar 32.
Definition e_d := EVar 33.
Definition DBX := EAluw ALU_SRL (EMd M_MUL (ELit 125613361) (EAlu ALU_AND (EAlu ALU_ADD (EVar 32) (ELit 1)) (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 32)) (ELit (-1))))) (ELit 27).
Definition sr_mc1 := (sr_upd (sr_upd (sr_upd sr_id 10 (e_s)) 11 (ELit 125613361)) 19 (ELit 98952)).
Definition kn_mc1 : list kentry :=
  [ KRange e_s 0 4294967295;
    KRange e_d 0 31;
    KRange DBX 0 31;
    KWord (SA DBX 98952) 1 e_d ].
Definition scr_mc1 : scripts := SCR [] [] [].
Definition ss_mc1 := SS 0x53e6c sr_mc1 [] kn_mc1 34.
Definition RUN_mc1 := sym_exec SEGS 100 true [0x53e9c] scr_mc1 ss_mc1 [].

Definition RES_mc1 := Eval vm_compute in RUN_mc1.
Lemma RES_mc1_ok : sym_exec SEGS 100 true [0x53e9c] scr_mc1 (SS 0x53e6c sr_mc1 [] kn_mc1 34) [] = RES_mc1.
Proof. vm_compute. reflexivity. Qed.
End AXF_mc1.

Module AXF_mc2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_u := EVar 32.
Definition e_x := EVar 33.
Definition e_i1 := EVar 34.
Definition e_t1 := EVar 35.
Definition sr_mc2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_x)) 11 (e_i1)) 12 (ELit 97932)) 20 (e_u)).
Definition kn_mc2 : list kentry :=
  [ KRange e_u 10 8190;
    KRange e_x 0 124;
    KRange e_i1 0 47;
    KRange e_t1 0 65535;
    KWord (SA (EMd M_MUL (ELit 2) e_i1) 98984) 2 e_t1 ].
Definition scr_mc2 : scripts := SCR [false] [] [].
Definition ss_mc2 := SS 0x53e9c sr_mc2 [] kn_mc2 36.
Definition RUN_mc2 := sym_exec SEGS 100 true [0x53f14] scr_mc2 ss_mc2 [].

Definition scr_mc2_T : scripts := SCR [true] [] [].
Definition RES_mc2_T := Eval vm_compute in sym_exec SEGS 100 true [0x53f14] scr_mc2_T ss_mc2 [].
Lemma RES_mc2_T_ok : sym_exec SEGS 100 true [0x53f14] scr_mc2_T (SS 0x53e9c sr_mc2 [] kn_mc2 36) [] = RES_mc2_T.
Proof. vm_compute. reflexivity. Qed.

Definition scr_mc2_F : scripts := SCR [false] [] [].
Definition RES_mc2_F := Eval vm_compute in sym_exec SEGS 100 true [0x53f14] scr_mc2_F ss_mc2 [].
Lemma RES_mc2_F_ok : sym_exec SEGS 100 true [0x53f14] scr_mc2_F (SS 0x53e9c sr_mc2 [] kn_mc2 36) [] = RES_mc2_F.
Proof. vm_compute. reflexivity. Qed.
End AXF_mc2.

Module AXF_mc3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_u := EVar 32.
Definition e_i2 := EVar 33.
Definition e_t2 := EVar 34.
Definition sr_mc3 := (sr_upd (sr_upd (sr_upd sr_id 11 (ELit 98984)) 12 (e_i2)) 20 (e_u)).
Definition kn_mc3 : list kentry :=
  [ KRange e_u 10 8190;
    KRange e_i2 0 47;
    KRange e_t2 0 65535;
    KWord (SA (EMd M_MUL (ELit 2) e_i2) 98984) 2 e_t2 ].
Definition scr_mc3 : scripts := SCR [] [] [].
Definition ss_mc3 := SS 0x53f14 sr_mc3 [] kn_mc3 35.
Definition RUN_mc3 := sym_exec SEGS 100 true [0x53f2c] scr_mc3 ss_mc3 [].

Definition RES_mc3 := Eval vm_compute in RUN_mc3.
Lemma RES_mc3_ok : sym_exec SEGS 100 true [0x53f2c] scr_mc3 (SS 0x53f14 sr_mc3 [] kn_mc3 35) [] = RES_mc3.
Proof. vm_compute. reflexivity. Qed.
End AXF_mc3.

Module AXF_mt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_G := EVar 33.
Definition e_idx := EVar 34.
Definition e_ctr := EVar 35.
Definition e_ra0 := EVar 36.
Definition e_s00 := EVar 37.
Definition e_s10 := EVar 38.
Definition e_s20 := EVar 39.
Definition e_s30 := EVar 40.
Definition e_s40 := EVar 41.
Definition sr_mt := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 18 (e_G)) 19 (e_idx)).
Definition kn_mt : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KRange e_n 1 (2^26);
    KRange e_G 1 (2^63-1);
    KRange e_idx 0 31;
    KRange e_ctr 0 (2^32-1);
    KWord (SA (ELit 0) 621732) 4 e_ctr;
    KWord (SA (ELit 0) 621712) 4 (ELit 0);
    KWord (SA (EVar 2) 40) 8 e_ra0;
    KWord (SA (EVar 2) 32) 8 e_s00;
    KWord (SA (EVar 2) 24) 8 e_s10;
    KWord (SA (EVar 2) 16) 8 e_s20;
    KWord (SA (EVar 2) 8) 8 e_s30;
    KWord (SA (EVar 2) 0) 8 e_s40 ].
Definition scr_mt : scripts := SCR [] [] [].
Definition ss_mt := SS 0x5405c sr_mt [] kn_mt 42.
Definition RUN_mt := sym_exec SEGS 100 true [0x5494c] scr_mt ss_mt [].

Definition RES_mt := Eval vm_compute in RUN_mt.
Lemma RES_mt_ok : sym_exec SEGS 100 true [0x5494c] scr_mt (SS 0x5405c sr_mt [] kn_mt 42) [] = RES_mt.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt.

Module AXF_mtz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mt.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record mt_pre (regs : bvmap 5 word) (m : word -> option byte) (n G idx ctr : Z) (wra ws0 ws1 ws2 ws3 ws4 : word) : Prop := {
  t_R8 : getr regs 8 = wa n ; t_R9 : getr regs 9 = wa 621712 ; t_R18 : getr regs 18 = wa G ; t_R19 : getr regs 19 = wa idx ;
  t_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ; t_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  t_Rn : 1 <= n <= 2^26 ; t_RG : 1 <= G <= 2^63-1 ; t_Ridx : 0 <= idx <= 31 ; t_Rctr : 0 <= ctr <= 2^32-1 ;
  t_Mctr : rdn SEGS m (wa (0 + 621732)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  t_Mlock : rdn SEGS m (wa (0 + 621712)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  t_Mra : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 40)) 8 = Some (word_to_le_bytes 8 wra) ;
  t_Ms0 : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 32)) 8 = Some (word_to_le_bytes 8 ws0) ;
  t_Ms1 : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 24)) 8 = Some (word_to_le_bytes 8 ws1) ;
  t_Ms2 : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 16)) 8 = Some (word_to_le_bytes 8 ws2) ;
  t_Ms3 : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 8)) 8 = Some (word_to_le_bytes 8 ws3) ;
  t_Ms4 : rdn SEGS m (wa (bv_unsigned (getr regs 2) + 0)) 8 = Some (word_to_le_bytes 8 ws4)
}.

Definition mt_regs (R regs : bvmap 5 word) (n G idx ctr : Z) (wra ws0 ws1 ws2 ws3 ws4 : word) : Prop :=
  getr R 10 = wa G /\ getr R 11 = wa idx /\ getr R 12 = wa n /\ getr R 13 = wa (bv_swrap 32 ctr) /\
  getr R 1 = wra /\ getr R 8 = ws0 /\ getr R 9 = ws1 /\ getr R 18 = ws2 /\ getr R 19 = ws3 /\ getr R 20 = ws4 /\
  getr R 2 = v_addi (getr regs 2) 48 /\
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

Section MT.
Context {fx : FPState}.

#[using="Type"] Theorem mt_arm : forall regs m rom n G idx ctr wra ws0 ws1 ws2 ws3 ws4, mt_pre regs m n G idx ctr wra ws0 ws1 ws2 ws3 ws4 ->
  exists R, msteps SEGS (mkst regs (wa 0x5405c) m rom) (mkst R (wa 0x5494c) m rom)
         /\ mt_regs R regs n G idx ctr wra ws0 ws1 ws2 ws3 ws4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n G idx ctr wra ws0 ws1 ws2 ws3 ws4 P.
  destruct P as [R8 R9 R18 R19 Rsp Asp Rn RG Ridx Rctr Mctr Mlock Mra Ms0 Ms1 Ms2 Ms3 Ms4].
  set (spz := bv_unsigned (getr regs 2)) in *.
  set (E := Env (reg_ev regs (fun k => wa (nth (k - 32) [n; G; idx; ctr; bv_unsigned wra; bv_unsigned ws0; bv_unsigned ws1;
                                                        bv_unsigned ws2; bv_unsigned ws3; bv_unsigned ws4] 0))) (fun _ => [])).
  assert (HR : regs_ok E sr_mt regs).
  { apply (regs_ok_pin _ _ regs 19); [apply (regs_ok_pin _ _ regs 18); [apply (regs_ok_pin _ _ regs 9);
      [apply (regs_ok_pin _ sr_id regs 8); [apply regs_ok_id|] |] |] |].
    - rewrite R8. reflexivity.
    - rewrite R9. reflexivity.
    - rewrite R18. reflexivity.
    - rewrite R19. reflexivity. }
  assert (Z2 : bv_unsigned (ev E 2) = spz) by reflexivity.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (W36 : ev E 36 = wra) by (apply wa_u).
  assert (W37 : ev E 37 = ws0) by (apply wa_u).
  assert (W38 : ev E 38 = ws1) by (apply wa_u).
  assert (W39 : ev E 39 = ws2) by (apply wa_u).
  assert (W40 : ev E 40 = ws3) by (apply wa_u).
  assert (W41 : ev E 41 = ws4) by (apply wa_u).
  assert (HK : know_ok SEGS E m kn_mt).
  { unfold know_ok, kn_mt.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
    all: cbn [zeval edenot e_n e_G e_idx e_ctr e_ra0 e_s00 e_s10 e_s20 e_s30 e_s40 a_base a_off].
    all: rewrite ?Z2, ?Z32, ?Z33, ?Z34, ?Z35, ?W36, ?W37, ?W38, ?W39, ?W40, ?W41.
    all: rewrite ?(mod64_of_range _ _ _ Rsp eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl),
           ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl).
    all: rewrite ?wa_u.
    all: first [ assumption | lia ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_mt))) by (cbn [RES_mt fst snd]; apply Forall_nil).
  destruct (run_sound SEGS 100 [0x5494c] scr_mt 0x5405c sr_mt kn_mt 42 _ _ _ E m rom regs RES_mt_ok HR HK Hsc)
    as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_mt fst snd s_pc s_log s_regs mem_denot] in Hms. exact Hms.
  - cbn [RES_mt fst snd s_regs] in HR'. clear Hms. unfold mt_regs.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    repeat split.
    all: try (srg HR'; first [ reflexivity | exact W36 | exact W37 | exact W38 | exact W39 | exact W40 | exact W41 ]).
    all: try (srg HR'; rewrite zeval_sound; unfold v_addi; f_equal; cbn [zeval edenot]; rewrite Z2; reflexivity).
    all: try (intros k Hk; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [ rewrite (HR' _); reflexivity |]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z35, (mod64_of_range _ _ _ Rctr eq_refl eq_refl); apply ext4_swrap.
Qed.

End MT.
End AXF_mtz.

Module AXF_nm0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_u := EVar 32.
Definition sr_nm0 := (sr_upd sr_id 14 (e_u)).
Definition kn_nm0 : list kentry :=
  [ KRange e_u 10 127 ].
Definition scr_nm0 : scripts := SCR [] [] [].
Definition ss_nm0 := SS 0x543c8 sr_nm0 [] kn_nm0 33.
Definition RUN_nm0 := sym_exec SEGS 100 true [0x543e8] scr_nm0 ss_nm0 [].

Definition scr_pnm0 : scripts := SCR [] [] [].
Definition RES_pnm0 := Eval vm_compute in sym_exec SEGS 100 true [0x543e8] scr_pnm0 ss_nm0 [].
Lemma RES_pnm0_ok : sym_exec SEGS 100 true [0x543e8] scr_pnm0 (SS 0x543c8 sr_nm0 [] kn_nm0 33) [] = RES_pnm0.
Proof. vm_compute. reflexivity. Qed.
End AXF_nm0.

Module AXF_nm0b.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_y := EVar 32.
Definition sr_nm0b := (sr_upd sr_id 10 (e_y)).
Definition kn_nm0b : list kentry :=
  [ KRange e_y 0 4294967295 ].
Definition scr_nm0b : scripts := SCR [] [] [].
Definition ss_nm0b := SS 0x543e8 sr_nm0b [] kn_nm0b 33.
Definition RUN_nm0b := sym_exec SEGS 100 true [0x54404] scr_nm0b ss_nm0b [].

Definition scr_pnm0b : scripts := SCR [] [] [].
Definition RES_pnm0b := Eval vm_compute in sym_exec SEGS 100 true [0x54404] scr_pnm0b ss_nm0b [].
Lemma RES_pnm0b_ok : sym_exec SEGS 100 true [0x54404] scr_pnm0b (SS 0x543e8 sr_nm0b [] kn_nm0b 33) [] = RES_pnm0b.
Proof. vm_compute. reflexivity. Qed.
End AXF_nm0b.

Module AXF_nm1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_s := EVar 32.
Definition e_d := EVar 33.
Definition DBX := EAluw ALU_SRL (EMd M_MUL (ELit 125613361) (EAlu ALU_AND (EAlu ALU_ADD (EVar 32) (ELit 1)) (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 32)) (ELit (-1))))) (ELit 27).
Definition sr_nm1 := (sr_upd (sr_upd sr_id 10 (e_s)) 12 (ELit 125612032)).
Definition kn_nm1 : list kentry :=
  [ KRange e_s 0 4294967295;
    KRange e_d 0 31;
    KRange DBX 0 31;
    KWord (SA DBX 98952) 1 e_d ].
Definition scr_nm1 : scripts := SCR [] [] [].
Definition ss_nm1 := SS 0x54404 sr_nm1 [] kn_nm1 34.
Definition RUN_nm1 := sym_exec SEGS 100 true [0x54434] scr_nm1 ss_nm1 [].

Definition scr_pnm1 : scripts := SCR [] [] [].
Definition RES_pnm1 := Eval vm_compute in sym_exec SEGS 100 true [0x54434] scr_pnm1 ss_nm1 [].
Lemma RES_pnm1_ok : sym_exec SEGS 100 true [0x54434] scr_pnm1 (SS 0x54404 sr_nm1 [] kn_nm1 34) [] = RES_pnm1.
Proof. vm_compute. reflexivity. Qed.
End AXF_nm1.

Module AXF_nm3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_u := EVar 32.
Definition e_i2 := EVar 33.
Definition e_t2 := EVar 34.
Definition sr_nm3 := (sr_upd (sr_upd (sr_upd sr_id 12 (e_i2)) 14 (e_u)) 25 (ELit 98984)).
Definition kn_nm3 : list kentry :=
  [ KRange e_u 10 127;
    KRange e_i2 0 47;
    KRange e_t2 0 65535;
    KWord (SA (EMd M_MUL (ELit 2) e_i2) 98984) 2 e_t2 ].
Definition scr_nm3 : scripts := SCR [] [] [].
Definition ss_nm3 := SS 0x54464 sr_nm3 [] kn_nm3 35.
Definition RUN_nm3 := sym_exec SEGS 100 true [0x5447c] scr_nm3 ss_nm3 [].

Definition scr_pnm3 : scripts := SCR [] [] [].
Definition RES_pnm3 := Eval vm_compute in sym_exec SEGS 100 true [0x5447c] scr_pnm3 ss_nm3 [].
Lemma RES_pnm3_ok : sym_exec SEGS 100 true [0x5447c] scr_pnm3 (SS 0x54464 sr_nm3 [] kn_nm3 35) [] = RES_pnm3.
Proof. vm_compute. reflexivity. Qed.
End AXF_nm3.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Record efb_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx n mem sz st off : Z) : Prop := {
  eb_R10 : getr regs 10 = wa G ; eb_R11 : getr regs 11 = wa idx ; eb_R12 : getr regs 12 = wa n ;
  eb_R14 : getr regs 14 = wa (16 * sz) ; eb_R15 : getr regs 15 = wa st ; eb_R16 : getr regs 16 = wa mem ; eb_R17 : getr regs 17 = wa off ;
  eb_RG : 1 <= G <= 2^63-1 ; eb_AG : G mod 8 = 0 ; eb_Ridx : 0 <= idx <= 31 ; eb_Rn : 1 <= n <= 2^26 ;
  eb_Rmem : 1 <= mem <= 2^63-1 ; eb_Rsz : 1 <= sz <= 2^23 ; eb_Rst : 17 <= st <= 2^63-1 ; eb_Roff : 0 <= off <= 255 ;
  eb_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ;
  eb_fit : n + 4 + 16 * off <= 16 * sz ;
  eb_Rend : st + 16 * sz <= 2^63 ;
  eb_Goff : 0 <= st - mem - 16 <= 2^30 ; eb_Aoff : (st - mem) mod 16 = 0 ;
  eb_W : forall d k, 0 <= d -> d + Z.of_nat k <= 16 * sz -> store_ok SEGS m (wa (st - 4 + d)) k = true ;
  eb_D : G + 16 + 8 <= st - 4 \/ st - 4 + 16 * sz <= G + 16
}.

Definition le (w : nat) (v : Z) : list byte := word_to_le_bytes w (wa v).

(* [comment removed for export] *)
Definition efb_rsv (sz n off : Z) : Z := 16 * sz - 4 - 16 * off - n.
Definition efb_code (rsv : Z) : Z := if rsv =? 0 then 0 else if rsv <? 5 then rsv else 5.
Definition efb_mem (m : word -> option byte) (idx n mem sz st off : Z) : word -> option byte :=
  let p := st + 16 * off in
  let e := st + 16 * sz - 4 in
  let rsv := efb_rsv sz n off in
  let m1 := if off =? 0 then m else wbytes (wbytes (wbytes m (wa (st - 3)) (le 1 224)) (wa (st - 2)) (le 2 off)) (wa (p - 4)) (le 1 0) in
  let m2 := wbytes (wbytes m1 (wa (p - 3)) (le 1 idx)) (wa (p - 2)) (le 2 ((p - mem - 16) / 16)) in
  let m3 := if rsv =? 0 then m2 else
              let m2' := wbytes m2 (wa (p + n)) (le 1 0) in
              if rsv <? 5 then m2' else wbytes (wbytes m2' (wa (e - 5)) (le 1 0)) (wa (e - 4)) (le 4 rsv) in
  wbytes m3 (wa (p - 3)) (le 1 (idx + 32 * efb_code rsv)).

Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (wa x) = x.
Proof.
  intros x Hx. unfold bv_signed, wa. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 `div` 2) with 9223372036854775808.
  rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma br_lt_z : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> branch_taken BC_LT (wa x) (wa y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_small by assumption. reflexivity. Qed.

Lemma landx31 : forall idx, 0 <= idx <= 31 -> Z.land idx 31 = idx.
Proof. intros idx H. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. cbn. lia. Qed.

Section EFB.
Context {fx : FPState}.

Definition efb_env (regs : bvmap 5 word) (G idx n mem sz st off : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [G; idx; n; mem; sz; st; off] 0))) (fun _ => []).

#[using="Type"] Lemma efb_regs_ok : forall regs m G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  regs_ok (efb_env regs G idx n mem sz st off) sr_efb regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n mem sz st off P. destruct P as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z38 : bv_unsigned (ev (efb_env regs G idx n mem sz st off) 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  apply (regs_ok_pin _ _ regs 17); [apply (regs_ok_pin _ _ regs 16); [apply (regs_ok_pin _ _ regs 15); [apply (regs_ok_pin _ _ regs 14);
    [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ _ regs 11); [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |] |] |] |] |].
  all: first [ rewrite R10 | rewrite R11 | rewrite R12 | rewrite R15 | rewrite R16 | rewrite R17 | rewrite R14 ]; try reflexivity.
  rewrite zeval_sound. cbn [zeval edenot STRIDE e_sz]. rewrite Z38. reflexivity.
Qed.

#[using="Type"] Lemma efb_know_ok : forall regs m G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  know_ok SEGS (efb_env regs G idx n mem sz st off) m kn_efb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n mem sz st off P. destruct P as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  set (E := efb_env regs G idx n mem sz st off).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold know_ok, kn_efb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot e_G e_idx e_n e_mem e_sz e_st e_off STRIDE P a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rst eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Roff eq_refl eq_refl).
  all: litmods.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (intros d k Hd Hk; replace (st + -4 + d) with (st - 4 + d) by ring; apply W; [exact Hd | clear - Hk Rsz; lia]).
  all: try (clear - D Rsz; lia).
  all: idtac "KREMAINING". all: match goal with |- ?g => idtac g end.
Qed.


#[using="Type"] Lemma edenot_subw : forall E a b, edenot E (EAluw ALU_SUB a b) = wa (bv_swrap 32 (zeval E a mod 2^64 - zeval E b mod 2^64)).
Proof. LiaFast.lf_pins LiaFast.u0. intros E a b. cbn [edenot]. rewrite w_subw. unfold v_subw. rewrite !zeval_sound, !u_wa. reflexivity. Qed.

#[using="Type"] Lemma swrap_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma shl4_small : forall x, 0 <= x <= 255 -> bv_swrap 32 (Z.shiftl x (4 mod 32)) = 16 * x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x Hx. change (4 mod 32) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. rewrite swrap_small by lia. ring. Qed.

Ltac efb_norm Z32 Z33 Z34 Z35 Z36 Z37 Z38 Roff Rsz Rst Rmem Rn Ridx :=
  cbn [zeval edenot a_base a_off]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38;
  rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl),
    ?(mod64_of_range _ _ _ Rst eq_refl eq_refl), ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl),
    ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl);
  rewrite ?shl4_small by exact Roff; litmods.



(* [comment removed for export] *)
Ltac efb_sc W Fit Rsz Roff Rn Rst D st :=
  first
  [ (apply sc_br_z; cbn [zeval edenot];
     repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end;
     rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl);
     rewrite ?shl4_small by exact Roff; litmods;
     rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z;
     rewrite ?br_lt_z by (clear - Fit Rn Rsz Roff; lia);
     first [ apply Z.eqb_eq | apply Z.eqb_neq | (rewrite negb_true_iff; apply Z.eqb_neq) | (rewrite negb_false_iff; apply Z.eqb_eq)
           | (rewrite negb_true_iff; apply Z.ltb_ge) | (rewrite negb_false_iff; apply Z.ltb_lt) | apply Z.ltb_lt | apply Z.ltb_ge ];
     repeat (rewrite Z.mod_small by (clear - Fit Rn Rsz Roff; lia));
     lia)
  | (cbn [sc_denot]; rewrite adenot_z; cbn [zeval edenot];
     repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end;
     rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl); rewrite ?shl4_small by exact Roff;
     match goal with |- store_ok _ _ (wa ?A) ?k = true =>
       replace A with (st - 4 + (A - (st - 4))) by ring; apply W; [ ((clear - Fit Rsz Roff Rn; lia) || lia) | ((clear - Fit Rsz Roff Rn; lia) || lia) ] end)
  | (cbn [sc_denot]; unfold flat, estart, elenZ; rewrite !zeval_sound, !u_wa;
     cbn [zeval edenot a_base a_off];
     repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end;
     rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl),
       ?(mod64_of_range _ _ _ Rst eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl);
     rewrite ?shl4_small by exact Roff; litmods;
     repeat match goal with |- context [ (?x mod 2^64) ] => rewrite (Z.mod_small x (2^64)) by (clear - Fit Rsz Roff Rn Rst; lia) end;
     lia) ].

(* [comment removed for export] *)
Ltac efb_ifs :=
  repeat match goal with
  | |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia)
                                   | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
  | |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
                                   | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
  end.

Ltac efb_norm_z Roff Rsz Rst Rmem Rn Ridx :=
  cbn [zeval edenot a_base a_off];
  repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end;
  rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl),
    ?(mod64_of_range _ _ _ Rst eq_refl eq_refl), ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl),
    ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl);
  rewrite ?shl4_small by exact Roff; litmods.

Ltac efb_addr Roff Rsz Rst Rmem Rn Ridx := rewrite adenot_z; efb_norm_z Roff Rsz Rst Rmem Rn Ridx; f_equal; lia.

Ltac efb_val Roff Rsz Rst Rmem Rn Ridx st off mem :=
  first [ reflexivity
        | (unfold le; rewrite zeval_sound; apply le_wa_eqm; [|apply Nat.leb_le; reflexivity];
           cbn [zeval a_base a_off]; rewrite ?edenot_subw, ?u_wa;
           efb_norm_z Roff Rsz Rst Rmem Rn Ridx;
           first [ (f_equal; lia)
                 | (repeat match goal with |- context [ (?x mod 2^64) ] => rewrite (Z.mod_small x (2^64)) by lia end;
                    rewrite swrap_small by lia;
                    repeat match goal with |- context [ (?x mod 2^64) ] => rewrite (Z.mod_small x (2^64)) by lia end;
                    rewrite Z.shiftr_div_pow2 by lia; f_equal; f_equal; lia) ]) ].

Ltac efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem :=
  first [ reflexivity
        | (apply (f_equal3 wbytes); [ efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem | efb_addr Roff Rsz Rst Rmem Rn Ridx | efb_val Roff Rsz Rst Rmem Rn Ridx st off mem ]) ].

#[using="Type"] Theorem efb_TT : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off = 0 /\ efb_rsv sz n off = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_TT))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_TT))).
  { cbn [RES_efb_TT fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_TT 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_TT_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_TT fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

#[using="Type"] Theorem efb_FT : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off <> 0 /\ efb_rsv sz n off = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_FT))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_FT))).
  { cbn [RES_efb_FT fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_FT 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_FT_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_FT fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

#[using="Type"] Theorem efb_TFT : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off = 0 /\ 0 < efb_rsv sz n off < 5 ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_TFT))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_TFT))).
  { cbn [RES_efb_TFT fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_TFT 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_TFT_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_TFT fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

#[using="Type"] Theorem efb_TFF : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off = 0 /\ 5 <= efb_rsv sz n off ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_TFF))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_TFF))).
  { cbn [RES_efb_TFF fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_TFF 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_TFF_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_TFF fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

#[using="Type"] Theorem efb_FFT : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off <> 0 /\ 0 < efb_rsv sz n off < 5 ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_FFT))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_FFT))).
  { cbn [RES_efb_FFT fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_FFT 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_FFT_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_FFT fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

#[using="Type"] Theorem efb_FFF : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  off <> 0 /\ 5 <= efb_rsv sz n off ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ regs_ok (efb_env regs G idx n mem sz st off) (s_regs (fst (fst RES_efb_FFF))) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P CC.
  pose proof (efb_regs_ok regs m G idx n mem sz st off P) as HR.
  pose proof (efb_know_ok regs m G idx n mem sz st off P) as HK.
  set (E := efb_env regs G idx n mem sz st off) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  unfold efb_rsv in *.
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_efb_FFF))).
  { cbn [RES_efb_FFF fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: efb_sc W Fit Rsz Roff Rn Rst D st. }
  destruct (run_sound SEGS 200 [] scr_efb_FFF 0x54a04 sr_efb kn_efb 39 _ _ _ E m rom regs RES_efb_FFF_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [|exact HR'].
  cbn [RES_efb_FFF fst snd s_pc s_log] in Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (efb_mem m idx n mem sz st off) with M; [exact Hms|] end.
  clear Hms HR'. cbn [mem_denot]. unfold efb_mem, efb_code, efb_rsv. cbv zeta.
  destruct CC as (C1 & C2). efb_ifs.
  efb_chain Roff Rsz Rst Rmem Rn Ridx st off mem.
Qed.

End EFB.

Section EFBU.
Context {fx : FPState}.

Definition callee_regs : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma efb_post_of : forall regs R G idx n mem sz st off sres,
  regs_ok (efb_env regs G idx n mem sz st off) sres R ->
  (forall k, In k callee_regs -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R G idx n mem sz st off sres HR Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev efb_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; cbn [callee_regs In] in Hk; lia). reflexivity.
Qed.

#[using="Type"] Theorem efb_arm : forall regs m rom G idx n mem sz st off, efb_pre regs m G idx n mem sz st off ->
  exists R, msteps SEGS (mkst regs (wa 0x54a04) m rom) (mkst R (wa 0x54a98) (efb_mem m idx n mem sz st off) rom)
         /\ getr R 10 = wa (st + 16 * off)
         /\ (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n mem sz st off P.
  pose proof P as P'. destruct P' as [R10 R11 R12 R14 R15 R16 R17 RG AG Ridx Rn Rmem Rsz Rst Roff Mmem Fit Rend Goff Aoff W D].
  assert (Z37 : bv_unsigned (ev (efb_env regs G idx n mem sz st off) 37) = st) by exact (u_wa_small _ (rng64 _ _ _ Rst eq_refl)).
  assert (Z38 : bv_unsigned (ev (efb_env regs G idx n mem sz st off) 38) = off) by exact (u_wa_small _ (rng64 _ _ _ Roff eq_refl)).
  destruct (Z.eq_dec off 0) as [O0|O0]; destruct (Z.eq_dec (efb_rsv sz n off) 0) as [V0|V0];
    [ | destruct (Z_lt_le_dec (efb_rsv sz n off) 5) as [V5|V5] | | destruct (Z_lt_le_dec (efb_rsv sz n off) 5) as [V5|V5] ].
  all: unfold efb_rsv in *.
  1: destruct (efb_TT regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; assumption)) as (R & Hms & HR').
  2: destruct (efb_TFT regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; [assumption | lia])) as (R & Hms & HR').
  3: destruct (efb_TFF regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; [assumption | lia])) as (R & Hms & HR').
  4: destruct (efb_FT regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; assumption)) as (R & Hms & HR').
  5: destruct (efb_FFT regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; [assumption | lia])) as (R & Hms & HR').
  6: destruct (efb_FFF regs m rom G idx n mem sz st off P ltac:(unfold efb_rsv; split; [assumption | lia])) as (R & Hms & HR').
  all: exists R; split; [exact Hms|]; split.
  all: try (apply (efb_post_of regs R G idx n mem sz st off _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
            repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
  all: cbn [RES_efb_TT RES_efb_TFT RES_efb_TFF RES_efb_FT RES_efb_FFT RES_efb_FFF fst snd s_regs] in HR'.
  all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z37, ?Z38;
       rewrite ?(mod64_of_range _ _ _ Roff eq_refl eq_refl); rewrite ?shl4_small by exact Roff; try lia.
Qed.

End EFBU.
