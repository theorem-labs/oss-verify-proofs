(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  ListFacts PropExec CatExec CatSim SeqExec StoreOk MallocDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Record enframe_post (RSEGS : list Segment) (mem' : word -> option byte) (idx n stride start off : Z) : Prop := EPOST {
  P_p := start + 16 * off;
  P_e := start + stride - 4;
  P_r := stride - 4 - n - 16 * off;
  P_q := stride * idx / 16 + off;
  Pm4   : mem' (Z_to_bv 64 (P_p - 4)) = Some (Z_to_bv 8 0);
  Pm3   : mem' (Z_to_bv 64 (P_p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code P_r));
  Pm2   : rdn RSEGS mem' (Z_to_bv 64 (P_p - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 P_q));
  Pzr   : 0 < P_r -> mem' (Z_to_bv 64 (P_p + n)) = Some (Z_to_bv 8 0);
  Pe5   : 5 <= P_r -> mem' (Z_to_bv 64 (P_e - 5)) = Some (Z_to_bv 8 0);
  Pe4   : 5 <= P_r -> rdn RSEGS mem' (Z_to_bv 64 (P_e - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 P_r));
  Ps3   : off <> 0 -> mem' (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224);
  Ps2   : off <> 0 -> rdn RSEGS mem' (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 off));
  Pr    : 0 <= P_r /\ 0 <= off <= 255 /\ 0 <= P_q < 65536 }.

