(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
Import ListNotations.
Open Scope Z_scope.

Section CrlsStmt.
Variable segs : list Segment.

Definition crls_W (frame sp S P : Z) : list (Z * Z) := [(sp - frame, sp); (S, S + 24); (P, P + 16)].

Definition crls_post (frame maxlen : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
(n k : Z) (str rest : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch (crls_W frame (bv_unsigned sp) S P) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ 0 <= n <= maxlen /\ Z.of_nat (length str) <= n /\ ~ In (Z_to_bv 8 0) str
/\ rw_cells segs m' S [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)]
/\ 0 <= k <= rem
/\ rw_cells segs m' P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))]
/\ bytes_at segs m' ptr data
/\ stk segs m' lo (bv_unsigned sp).

Definition crls_stmt (entry frame : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(S P ptr rem lo maxlen : Z) (junk data : list byte),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 maxlen -> 1 <= maxlen <= 20 ->
rw_cells segs m S [CB 24 junk] ->
rw_cells segs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] ->
bytes_at segs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - frame ->

bv_unsigned sp <= S -> S + 24 <= P -> ptr + rem <= bv_unsigned sp - frame ->
mem_inv segs m ->
evt segs (crls_post frame maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition fdp_W (sp P : Z) : list (Z * Z) := [(sp - 16, sp); (P + 8, P + 16)].

Definition fdp_post (vmax kmax : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch (fdp_W (bv_unsigned sp) P) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ bv_unsigned a0 <= vmax
/\ rw_cells segs m' P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (Z.max (rem - kmax) 0))]
/\ bytes_at segs m' ptr data
/\ stk segs m' lo (bv_unsigned sp).

Definition fdp_pre (a0 sp : word) (P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : Prop :=
a0 = Z_to_bv 64 P /\
rw_cells segs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] /\
bytes_at segs m ptr data /\ Z.of_nat (length data) = rem /\ 0 < ptr /\
stk segs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - 16 /\
bv_unsigned sp <= P /\ ptr + rem <= bv_unsigned sp - 16 /\
mem_inv segs m.

Definition ciir10_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
fdp_pre a0 sp P ptr rem lo data m -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 10 ->
evt segs (fdp_post 10 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition ciiint_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
fdp_pre a0 sp P ptr rem lo data m -> bv_unsigned a1 = 2^64 - 2^31 -> bv_unsigned a2 = 2^31 - 1 ->
evt segs (fdp_post (2^64 - 1) 4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
End CrlsStmt.

Definition CRLS_P : Z := 0x212d0.  Definition CRLS_FRAME_P : Z := 128.
