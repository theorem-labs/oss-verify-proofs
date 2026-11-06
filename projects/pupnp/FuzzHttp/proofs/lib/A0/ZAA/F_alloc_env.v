(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim PEnv.
Import ListNotations.
Open Scope Z_scope.

Notation INST_MAXMALLOC := 725176%Z.
Notation AF_MALLOCFILL := 725284%Z.
Notation AF_FILLBYTE := 725292%Z.
Notation AF_PARTIAL := 725325%Z.
Notation RSS_EXCEEDED := 1268578%Z.
Notation GOT_LSAN_OFF := 699688%Z.
Notation LSAN_DISABLED := 6187392%Z.

Definition alloc_env (m : mem) : Prop :=
  rw_cells asegs m INST_MAXMALLOC [C8 (wz 1099511627776); C2 (wz 16); C2 (wz 2048)]
  /\ rw_cells asegs m AF_MALLOCFILL [C4 (wz 4096)]
  /\ rw_cells asegs m AF_FILLBYTE [C4 (wz 190)]
  /\ rw_cells asegs m AF_PARTIAL [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m RSS_EXCEEDED [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m GOT_LSAN_OFF [C8 (wz 16)]
  /\ rw_cells asegs m LSAN_DISABLED [C4 (wz 0)].

Definition alloc_env_cells : list (Z * Z) :=
  [(INST_MAXMALLOC, 12); (AF_MALLOCFILL, 4); (AF_FILLBYTE, 4); (AF_PARTIAL, 1); (RSS_EXCEEDED, 1); (GOT_LSAN_OFF, 8); (LSAN_DISABLED, 4)].

Definition alloc_env_clear (W : list (Z * Z)) : Prop :=
  Forall (fun iv => Forall (fun c => snd iv <= fst c \/ fst c + snd c <= fst iv) alloc_env_cells) W.

Ltac ae_split AE :=
  let H1 := fresh "AE_max" in let H2 := fresh "AE_fill" in let H3 := fresh "AE_fillb" in let H4 := fresh "AE_partial" in
  let H5 := fresh "AE_rss" in let H6 := fresh "AE_gotlsan" in let H7 := fresh "AE_lsan" in
  destruct AE as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
