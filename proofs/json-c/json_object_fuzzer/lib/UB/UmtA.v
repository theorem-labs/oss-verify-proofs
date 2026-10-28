(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh14.
Import ListNotations.
Open Scope Z_scope.

Section FdpJoStmt.
Variable segs : list Segment.

Definition fdp_preS (stkb : Z) (a0 sp : word) (P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : Prop :=
a0 = Z_to_bv 64 P /\
rw_cells segs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] /\
bytes_at segs m ptr data /\ Z.of_nat (length data) = rem /\ 0 < ptr /\
stk segs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp <= P /\ ptr + rem <= bv_unsigned sp - stkb /\
mem_inv segs m.

Definition fdp_WS (stkb sp P : Z) : list (Z * Z) := [(sp - stkb, sp); (P + 8, P + 16)].

Definition cii_stmt (entry kmax A1 A2 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
fdp_pre segs a0 sp P ptr rem lo data m -> bv_unsigned a1 = A1 -> bv_unsigned a2 = A2 ->
evt segs (fdp_post segs (2^64 - 1) kmax ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition fdp_postF (stkb kmax : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)
/\ fsaved F F' /\ frm0 fc'
/\ munch (fdp_WS stkb (bv_unsigned sp) P) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (Z.max (rem - kmax) 0))]
/\ bytes_at segs m' ptr data
/\ stk segs m' lo (bv_unsigned sp).

Definition cfp_stmt (entry stkb ihi : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
fdp_preS stkb a0 sp P ptr rem lo data m -> ihi <= lo ->
Sem.reg_get F (Z_to_bv 5 10) = Z_to_bv 64 0xFFEFFFFFFFFFFFFF ->
Sem.reg_get F (Z_to_bv 5 11) = Z_to_bv 64 0x7FEFFFFFFFFFFFFF ->
frm0 fc ->
evt segs (fdp_postF stkb 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
End FdpJoStmt.

Definition CFP_P : Z := 0x21874.  Definition CFP_STK_P : Z := 64.  Definition IHI_P : Z := 0x99000.
