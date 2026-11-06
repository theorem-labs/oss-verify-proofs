(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zks Sj_rtf Zwn Zwd Z106 Zw3
  Zz9 Zze Zzr Zzz Zzw.
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

