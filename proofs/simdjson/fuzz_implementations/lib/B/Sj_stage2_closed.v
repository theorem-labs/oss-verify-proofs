(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface Sj_rtf Sj_stage2_iface Sj_stage2_defs Sj_stage2_world Sj_stage2_adapt
  Sj_stage2_stra2 Sj_stage2_strb2 Sj_stage2_stro2 Sj_stage2_strv2 Sj_stage2_strr2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem stage2at_closed : forall RT, art_facts RT -> rt_contracts_f RT -> numa_stmt RT -> numo_stmt RT -> rootnum_stmt RT -> stage2at_cps RT.
Proof.
  intros RT AF RTF HNUMA HNUMO HROOT.
  apply (stage2at_ok RT AF RTF HNUMA HNUMO HROOT).
  - intros E Q s OK SHZ HI HD HQ GLT GLS KX KE. exact (seg_key_a E OK SHZ Q s HI HD HQ GLT GLS KX KE).
  - intros E Q s0 OK SHZ HI HC HQ GLT GLS KX KE. exact (seg_key_b E OK SHZ Q s0 HI HC HQ GLT GLS KX KE).
  - intros E Q s OK SHZ HK HW HSB HD HQ GLT GLS KX KE. exact (seg_str_o E OK SHZ Q s HK HW HSB HD HQ GLT GLS KX KE).
  - intros E Q s OK SHZ HI HQ GLT GLS KX KE. exact (seg_str_a E OK SHZ Q s HI HQ GLT GLS KX KE).
  - intros E Q OK SHZ CC HR HQ GLT GLS KX KE. exact (seg_root_str E OK SHZ CC HR Q HQ GLT GLS KX KE).
Qed.

Theorem stage2a_closed : forall RT, art_facts RT -> rt_contracts_f RT -> numa_stmt RT -> numo_stmt RT -> rootnum_stmt RT -> stage2a_cps RT.
Proof. intros RT AF RTF HNUMA HNUMO HROOT. apply stage2a_of_stage2at. exact (stage2at_closed RT AF RTF HNUMA HNUMO HROOT). Qed.

