(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TargetStmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable ENTRY : Z.

Variable G : (word -> option byte) -> Prop.
Notation segs := (hl_segs L).
Notation HEAPx := (HEAP L HIx).

Definition T_LOCCELL : Z := hl_tp L - 48.
Definition T_GLOBLOC : Z := hl_libc L + 56.
Definition T_LOCALE_LOCK : Z := hl_libc L + 0xd8.

Definition TGT_STACK : Z := 0x100000.

Definition xtgt (a : Z) : Prop := hl_volatile L a \/ (T_LOCCELL <= a < T_LOCCELL + 8).

Definition target_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (data size lo : Z) (payload : list byte) (errv : word),
HEAPx A LB m md ->

bytes_at segs m data payload -> Z.of_nat (length payload) = size ->
0 <= size < 2^26 -> 0 < data -> data + size < 2^63 ->
data + size <= alloc_ceiling ->
(size = 0 \/ In (data, size) LB) ->

rw_cells segs m T_LOCCELL [C8 (Z_to_bv 64 T_GLOBLOC)] ->
rw_cells segs m T_LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
G m ->

stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - TGT_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx -> hi_top L HIx < 2^62 ->
rw_cells segs m (hl_tp L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned ra mod 2 = 0 ->
frm0 fc ->
a0 = Z_to_bv 64 data -> a1 = Z_to_bv 64 size ->
(forall ms' m' md' (A' : AS L HIx) (errv' : word) (gp' : word) (LK : list blk),
ret_statew L ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_presx L xtgt LB (bv_unsigned sp) m m' ->
rw_cells segs m' T_LOCCELL [C8 (Z_to_bv 64 T_GLOBLOC)] ->
rw_cells segs m' (hl_tp L - 164) [C4 errv'] ->
G m' ->
HEAPx A' (LB ++ LK) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) md) T.
End TargetStmt.
End RC__1.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.
Goal T_LOCCELL S4L = 0x75e40 /\ T_GLOBLOC S4L = 0x96138 /\ T_LOCALE_LOCK S4L = 0x961d8
/\ T_LOCCELL U4L = 0x77bd0 /\ T_GLOBLOC U4L = 0x97ec8 /\ T_LOCALE_LOCK U4L = 0x97f68.
Proof. repeat split; reflexivity. Qed.

End RC__2.
