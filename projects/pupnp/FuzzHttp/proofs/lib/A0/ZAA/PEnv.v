(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
Import ListNotations.
Open Scope Z_scope.

Notation GOT_CF := 696512%Z.
Notation CF := 1332264%Z.
Notation CF_CLEAR_THR := 1332384%Z.
Notation CF_LIMIT := 1332408%Z.
Notation CF_DECOR := 1332524%Z.
Notation GOT_AF := 696520%Z.
Notation AF := 725240%Z.
Notation AF_PSG := 725318%Z.
Notation GOT_SHB := 696528%Z.
Notation SHB_CELL := 735480%Z.
Notation GOT_MIDB := 696536%Z.
Notation GOT_MIDE := 696544%Z.
Notation GOT_HME := 696552%Z.
Notation HME_CELL := 738784%Z.
Notation GOT_RMS := 696560%Z.
Notation RMS_CELL := 704384%Z.
Notation A0_MEMSET := 664092%Z.
Notation CANPOISON := 733532%Z.
Notation SEALED := 696592%Z.
Notation GOT_PAGE := 696496%Z.
Notation PAGE_CELL := 1323936%Z.

Notation CF_DONTDUMP := 1332483%Z.
Notation CF_NOHUGE := 1332508%Z.
Notation GOT_GUARD := 699752%Z.
Notation GUARD_CELL := 6318512%Z.
Notation LIBC_PAGESIZE := 6319152%Z.

Record penv := mkPEnv { pe_canary : word; pe_dontdump : Z; pe_nohuge : Z }.

Definition poison_env (E : penv) (m : word -> option byte) : Prop :=
  rw_cells asegs m GOT_CF [C8 (wz CF)]
  /\ rw_cells asegs m CF_CLEAR_THR [C8 (wz 18446744073709551615)]
  /\ rw_cells asegs m CF_LIMIT [C8 (wz 0)]
  /\ rw_cells asegs m CF_DECOR [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m GOT_AF [C8 (wz AF)]
  /\ rw_cells asegs m AF_PSG [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m GOT_SHB [C8 (wz SHB_CELL)]
  /\ rw_cells asegs m SHB_CELL [C8 (wz 2147450880)]
  /\ rw_cells asegs m GOT_MIDB [C8 (wz 738792); C8 (wz 738800); C8 (wz HME_CELL); C8 (wz RMS_CELL)]

  /\ rw_cells asegs m HME_CELL [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m RMS_CELL [C8 (wz A0_MEMSET)]
  /\ rw_cells asegs m CANPOISON [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m SEALED [C8 (wz 1)]
  /\ rw_cells asegs m GOT_PAGE [C8 (wz PAGE_CELL)]
  /\ rw_cells asegs m PAGE_CELL [C8 (wz 4096)]
  /\ rw_cells asegs m CF_DONTDUMP [C1 (Z_to_bv 8 (pe_dontdump E))]
  /\ rw_cells asegs m CF_NOHUGE [C1 (Z_to_bv 8 (pe_nohuge E))]
  /\ rw_cells asegs m GOT_GUARD [C8 (wz GUARD_CELL)]
  /\ rw_cells asegs m GUARD_CELL [C8 (pe_canary E)]
  /\ rw_cells asegs m LIBC_PAGESIZE [C8 (wz 4096)]
  /\ 0 <= pe_dontdump E < 256 /\ 0 <= pe_nohuge E < 256.

Ltac pe_split PE :=
  let H1 := fresh "PE_gotcf" in let H2 := fresh "PE_thr" in let H3 := fresh "PE_limit" in let H4 := fresh "PE_decor" in
  let H5 := fresh "PE_gotaf" in let H6 := fresh "PE_psg" in let H7 := fresh "PE_gotshb" in let H8 := fresh "PE_shb" in
  let H9 := fresh "PE_gotmem" in let H10 := fresh "PE_hme" in let H11 := fresh "PE_rms" in let H12 := fresh "PE_canp" in
  let H13 := fresh "PE_sealed" in let H14 := fresh "PE_gotpg" in let H15 := fresh "PE_pg" in
  let H16 := fresh "PE_dd" in let H17 := fresh "PE_nh" in let H18 := fresh "PE_gotguard" in let H19 := fresh "PE_guard" in
  let H20 := fresh "PE_libcpg" in let H21 := fresh "PE_ddr" in let H22 := fresh "PE_nhr" in
  destruct PE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22).

Ltac pe_join :=
  lazymatch goal with
  | |- poison_env _ _ =>
      unfold poison_env; repeat (first [ eassumption | lazymatch goal with |- _ /\ _ => split; [eassumption|] end ])
  | |- _ => idtac
  end.
