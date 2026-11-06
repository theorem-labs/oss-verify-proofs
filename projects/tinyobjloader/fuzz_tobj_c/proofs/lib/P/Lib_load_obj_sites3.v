(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "sOf"; "pH"; "E_fa"; "E_fl"; "@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Init.Datatypes"; "nil"; "prod"; "cons"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "P_fail"; "P_ok"; "Pre_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3"; "Ev_fs"; "Ev_cv"; "s_fs"; "Ev_ad0"; "Ev_ad1"; "Ev_ad2"; "Ev_ad3"; "Ev_ad4"; "Ev_ad5"; "Ev_ad6"; "s_cv"; "Ev_bd"; "s_ad0"; "s_ad1"; "s_ad2"; "s_ad3"; "s_ad4"; "s_ad5"; "s_ad6"; "s_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "Pre_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "sFR"; "sFS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Pre_bd"; "bcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy BuilderDispose ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Definition Ev_fs : sstate := Eval vm_compute in view vFS E_fs.
Definition s_fs : wsub := ltac2:(tb__ "0|0|
S3SfS2eS26A3").
Definition R_fs : list sobj := Eval vm_compute in R_of Ev_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.Pre_fs sFS.
Definition T_fsa : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs s_fs R_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.P_nop).
Definition is_fsa : wsub := ltac2:(tb__ "0|0|
S2S11Pc8S2cS0SfA1A4").
Definition tvT_fsa : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fsa P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fsa : amode := Eval vm_compute in am_subst is_fsa P.Lib_finalize__G1.Lib_finalize_shape_defs.ahd.
Definition T_fsb : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs s_fs R_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.P_ok).
Definition is_fsb : wsub := ltac2:(tb__ "0|0|
S2S11Pc8S2dS0SfA1A4").
Definition tvT_fsb : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fsb P.Lib_finalize__G1.Lib_finalize_shape_defs.tvOK).
Definition amT_fsb : amode := Eval vm_compute in am_subst is_fsb P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.
Definition T_fsc : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs s_fs R_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.P_fail).
Definition is_fsc : wsub := ltac2:(tb__ "0|0|
S2S11Pc8S2aS0SfA1A4").
Definition tvT_fsc : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fsc P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fsc : amode := Eval vm_compute in am_subst is_fsc P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.
Definition T_fsd : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_fs s_fs R_fs P.Lib_finalize__G1.Lib_finalize_shape_defs.P_failz).
Definition is_fsd : wsub := ltac2:(tb__ "0|0|
S2S11Pc8S2bS0SfA1A4").
Definition tvT_fsd : list (sv * sv) := Eval vm_compute in tvfill [7; 8; 9; 10; 11; 12; 13; 6; 19]%nat (import_tv is_fsd P.Lib_finalize__G1.Lib_finalize_shape_defs.tv0).
Definition amT_fsd : amode := Eval vm_compute in am_subst is_fsd P.Lib_finalize__G1.Lib_finalize_shape_defs.amq.

Definition Ev_cv : sstate := Eval vm_compute in view (vVR 280) E_cv.
Definition s_cv : wsub := ltac2:(tb__ "0|1|
S3S10S32SaS9S7S1A2M0SbS7S1P63S4A4S8G0A1A3A3").
Definition R_cv : list sobj := Eval vm_compute in R_of Ev_cv P.Lib_vec__G1.Lib_vec_reserve.Pre_vr [(99%positive, pH)].
Definition T_cvk : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_cv s_cv R_cv P.Lib_vec__G1.Lib_vec_reserve.P_keep).
Definition is_cvk : wsub := ltac2:(tb__ "0|0|
S2S19P64S31S0S10A1A4").
Definition tvT_cvk : list (sv * sv) := Eval vm_compute in tvfill [5]%nat (import_tv is_cvk P.Lib_vec__G1.Lib_vec_reserve.tv0).
Definition T_cvf : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_cv s_cv R_cv P.Lib_vec__G1.Lib_vec_reserve.P_fail).
Definition is_cvf : wsub := ltac2:(tb__ "0|0|
S2S19P64S2fS0S10A1A4").
Definition tvT_cvf : list (sv * sv) := Eval vm_compute in tvfill [5]%nat (import_tv is_cvf P.Lib_vec__G1.Lib_vec_reserve.tv0).
Definition T_cvg : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_cv s_cv R_cv P.Lib_vec__G1.Lib_vec_reserve.P_grown).
Definition is_cvg : wsub := ltac2:(tb__ "0|0|
S2S19P64S30S0S10A1A4").
Definition tvT_cvg : list (sv * sv) := Eval vm_compute in tvfill [5]%nat (import_tv is_cvg P.Lib_vec__G1.Lib_vec_reserve.tv_post).

Definition Ev_ad0 : sstate := Eval vm_compute in view vAD (E_adf 0).
Definition s_ad0 : wsub := ltac2:(tb__ "0|0|
S3S12SeS8S9S7S1A2A1A3").
Definition R_ad0 : list sobj := Eval vm_compute in R_of Ev_ad0 Lib_arena_dup.Pre_ad [].
Definition T_adf0 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad0 s_ad0 R_ad0 Lib_arena_dup.P_fail).
Definition is_ad0f : wsub := ltac2:(tb__ "0|0|
S2S1bP64ScS0S12A1A4").
Definition tvT_adf0 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad0f Lib_arena_dup.tv0).
Definition amT_adf0 : amode := Eval vm_compute in am_subst is_ad0f Lib_arena_dup.ahd.
Definition T_ado0 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad0 s_ad0 R_ad0 Lib_arena_dup.P_ok).
Definition is_ad0o : wsub := ltac2:(tb__ "0|0|
S2S1bP64SdS0S12A1A4").
Definition tvT_ado0 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad0o Lib_arena_dup.tv0).
Definition amT_ado0 : amode := Eval vm_compute in am_subst is_ad0o Lib_arena_dup.am_ok.

Definition Ev_ad1 : sstate := Eval vm_compute in view vAD (E_adf 1).
Definition s_ad1 : wsub := ltac2:(tb__ "0|0|
S3S13SeS8S9S7S1A2A1A3").
Definition R_ad1 : list sobj := Eval vm_compute in R_of Ev_ad1 Lib_arena_dup.Pre_ad [].
Definition T_adf1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad1 s_ad1 R_ad1 Lib_arena_dup.P_fail).
Definition is_ad1f : wsub := ltac2:(tb__ "0|0|
S2S1cP64ScS0S13A1A4").
Definition tvT_adf1 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad1f Lib_arena_dup.tv0).
Definition amT_adf1 : amode := Eval vm_compute in am_subst is_ad1f Lib_arena_dup.ahd.
Definition T_ado1 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad1 s_ad1 R_ad1 Lib_arena_dup.P_ok).
Definition is_ad1o : wsub := ltac2:(tb__ "0|0|
S2S1cP64SdS0S13A1A4").
Definition tvT_ado1 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad1o Lib_arena_dup.tv0).
Definition amT_ado1 : amode := Eval vm_compute in am_subst is_ad1o Lib_arena_dup.am_ok.

Definition Ev_ad2 : sstate := Eval vm_compute in view vAD (E_adf 2).
Definition s_ad2 : wsub := ltac2:(tb__ "0|0|
S3S14SeS8S9S7S1A2A1A3").
Definition R_ad2 : list sobj := Eval vm_compute in R_of Ev_ad2 Lib_arena_dup.Pre_ad [].
Definition T_adf2 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad2 s_ad2 R_ad2 Lib_arena_dup.P_fail).
Definition is_ad2f : wsub := ltac2:(tb__ "0|0|
S2S1dP64ScS0S14A1A4").
Definition tvT_adf2 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad2f Lib_arena_dup.tv0).
Definition amT_adf2 : amode := Eval vm_compute in am_subst is_ad2f Lib_arena_dup.ahd.
Definition T_ado2 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad2 s_ad2 R_ad2 Lib_arena_dup.P_ok).
Definition is_ad2o : wsub := ltac2:(tb__ "0|0|
S2S1dP64SdS0S14A1A4").
Definition tvT_ado2 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad2o Lib_arena_dup.tv0).
Definition amT_ado2 : amode := Eval vm_compute in am_subst is_ad2o Lib_arena_dup.am_ok.

Definition Ev_ad3 : sstate := Eval vm_compute in view vAD (E_adf 3).
Definition s_ad3 : wsub := ltac2:(tb__ "0|0|
S3S15SeS8S9S7S1A2A1A3").
Definition R_ad3 : list sobj := Eval vm_compute in R_of Ev_ad3 Lib_arena_dup.Pre_ad [].
Definition T_adf3 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad3 s_ad3 R_ad3 Lib_arena_dup.P_fail).
Definition is_ad3f : wsub := ltac2:(tb__ "0|0|
S2S1eP64ScS0S15A1A4").
Definition tvT_adf3 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad3f Lib_arena_dup.tv0).
Definition amT_adf3 : amode := Eval vm_compute in am_subst is_ad3f Lib_arena_dup.ahd.
Definition T_ado3 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad3 s_ad3 R_ad3 Lib_arena_dup.P_ok).
Definition is_ad3o : wsub := ltac2:(tb__ "0|0|
S2S1eP64SdS0S15A1A4").
Definition tvT_ado3 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad3o Lib_arena_dup.tv0).
Definition amT_ado3 : amode := Eval vm_compute in am_subst is_ad3o Lib_arena_dup.am_ok.

Definition Ev_ad4 : sstate := Eval vm_compute in view vAD (E_adf 4).
Definition s_ad4 : wsub := ltac2:(tb__ "0|0|
S3S16SeS8S9S7S1A2A1A3").
Definition R_ad4 : list sobj := Eval vm_compute in R_of Ev_ad4 Lib_arena_dup.Pre_ad [].
Definition T_adf4 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad4 s_ad4 R_ad4 Lib_arena_dup.P_fail).
Definition is_ad4f : wsub := ltac2:(tb__ "0|0|
S2S1fP64ScS0S16A1A4").
Definition tvT_adf4 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad4f Lib_arena_dup.tv0).
Definition amT_adf4 : amode := Eval vm_compute in am_subst is_ad4f Lib_arena_dup.ahd.
Definition T_ado4 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad4 s_ad4 R_ad4 Lib_arena_dup.P_ok).
Definition is_ad4o : wsub := ltac2:(tb__ "0|0|
S2S1fP64SdS0S16A1A4").
Definition tvT_ado4 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad4o Lib_arena_dup.tv0).
Definition amT_ado4 : amode := Eval vm_compute in am_subst is_ad4o Lib_arena_dup.am_ok.

Definition Ev_ad5 : sstate := Eval vm_compute in view vAD (E_adf 5).
Definition s_ad5 : wsub := ltac2:(tb__ "0|0|
S3S17SeS8S9S7S1A2A1A3").
Definition R_ad5 : list sobj := Eval vm_compute in R_of Ev_ad5 Lib_arena_dup.Pre_ad [].
Definition T_adf5 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad5 s_ad5 R_ad5 Lib_arena_dup.P_fail).
Definition is_ad5f : wsub := ltac2:(tb__ "0|0|
S2S20P64ScS0S17A1A4").
Definition tvT_adf5 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad5f Lib_arena_dup.tv0).
Definition amT_adf5 : amode := Eval vm_compute in am_subst is_ad5f Lib_arena_dup.ahd.
Definition T_ado5 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad5 s_ad5 R_ad5 Lib_arena_dup.P_ok).
Definition is_ad5o : wsub := ltac2:(tb__ "0|0|
S2S20P64SdS0S17A1A4").
Definition tvT_ado5 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad5o Lib_arena_dup.tv0).
Definition amT_ado5 : amode := Eval vm_compute in am_subst is_ad5o Lib_arena_dup.am_ok.

Definition Ev_ad6 : sstate := Eval vm_compute in view vAD (E_adf 6).
Definition s_ad6 : wsub := ltac2:(tb__ "0|0|
S3S18SeS8S9S7S1A2A1A3").
Definition R_ad6 : list sobj := Eval vm_compute in R_of Ev_ad6 Lib_arena_dup.Pre_ad [].
Definition T_adf6 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad6 s_ad6 R_ad6 Lib_arena_dup.P_fail).
Definition is_ad6f : wsub := ltac2:(tb__ "0|0|
S2S21P64ScS0S18A1A4").
Definition tvT_adf6 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad6f Lib_arena_dup.tv0).
Definition amT_adf6 : amode := Eval vm_compute in am_subst is_ad6f Lib_arena_dup.ahd.
Definition T_ado6 : sstate := Eval vm_compute in renorm (T_afterN 100 Ev_ad6 s_ad6 R_ad6 Lib_arena_dup.P_ok).
Definition is_ad6o : wsub := ltac2:(tb__ "0|0|
S2S21P64SdS0S18A1A4").
Definition tvT_ado6 : list (sv * sv) := Eval vm_compute in tvfill [19]%nat (import_tv is_ad6o Lib_arena_dup.tv0).
Definition amT_ado6 : amode := Eval vm_compute in am_subst is_ad6o Lib_arena_dup.am_ok.

Definition Ev_bd : sstate := Eval vm_compute in view vBD E_bd.
Definition s_bd : wsub := ltac2:(tb__ "0|1|
S3S1aS28SaS9S7S1A2M0SbS7S1Pc7S4A4S8G0A1A3A3").
Definition R_bd : list sobj := Eval vm_compute in R_of Ev_bd Lib_builder_dispose.Pre_bd [(199%positive, pH)].
Definition T_bd : sstate := Eval vm_compute in renorm (T_afterN 200 Ev_bd s_bd R_bd (BuilderDispose.P_bd Lib_builder_dispose.bcP)).
Definition is_bd : wsub := ltac2:(tb__ "0|0|
S2S22Pc8S27S29A1S0S1aA1A4").
Definition tvT_bd : list (sv * sv) := Eval vm_compute in tvfill [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%nat (import_tv is_bd tv0).

Definition s_fl : wsub := ltac2:(tb__ "0|0|
S3S6S24S23A1S25A3").
Definition R_fl : list sobj := Eval vm_compute in R_of E_fl (Pre_free EC_P) sFR.
Definition T_fl : sstate := Eval vm_compute in renorm (T_after E_fl s_fl R_fl (L_free EC_P)).

Definition s_fa : wsub := ltac2:(tb__ "0|0|
S3S5S24S23A1S25A3").
Definition R_fa : list sobj := Eval vm_compute in R_of E_fa (Pre_free EC_P) sFR.
Definition T_fa : sstate := Eval vm_compute in renorm (T_after E_fa s_fa R_fa (L_free EC_P)).
