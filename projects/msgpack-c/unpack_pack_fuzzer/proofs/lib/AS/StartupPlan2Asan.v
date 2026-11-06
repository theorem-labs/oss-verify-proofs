(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_r0_1 : plan :=
  PRun [0x4a154]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x8c6e8]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_r1_2 : plan :=
  PRun [0x4a154]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin  )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x8c6e8]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_r0_1)
  (startup2_plan_r1_2)).

Definition startup2_plan_ranges : list (Z * nat) := [(0x3b000, 1040%nat); (0x49000, 5136%nat); (0x5f000, 2064%nat); (0x64000, 3088%nat); (0x68000, 1040%nat); (0x6a000, 1040%nat); (0x6c000, 1040%nat); (0x6f000, 4112%nat); (0x78000, 1040%nat); (0x7c000, 4112%nat); (0x8c000, 1040%nat); (0x98000, 1040%nat); (0xbd000, 1040%nat); (0xc7000, 1040%nat); (0xc9000, 1040%nat)]%Z.
