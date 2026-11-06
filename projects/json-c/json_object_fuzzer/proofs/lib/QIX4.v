(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qazd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section P.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_delete_tail_post2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) svs',
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x75e70 - 164) [C4 errv] /\
lh_open rsegs S4F m' t tbl size (firstn jf es) svs' /\ HEAPx A' (lh_blocks t tbl size (firstn jf es) ++ LB) m' md'.

Definition lh_delete_tail_stmt2 : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv) (jf : nat) (ef : lent),
HEAPx A (lh_blocks t tbl size es ++ LB) m md ->
lh_open rsegs S4F m t tbl size es svs ->
nth_error es jf = Some ef -> (forall j x, (jf <= j)%nat -> nth_error es j = Some x -> le_v x = 0) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] -> tp = Z_to_bv 64 0x75e70 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
(forall ms' md', lh_delete_tail_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv t tbl size es jf ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x26d9c) fc None m (seg_rom rsegs)) md) T.
End P.

Section U.
Variable HIx : heap_iface U4L.
Notation HEAPx := (HEAP U4L HIx).

Definition u_lh_delete_tail_post2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) svs',
ret_state U4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only md md' /\ stk usegs m' lo (bv_unsigned sp) /\ heap_pres U4L LB (bv_unsigned sp) m m' /\
rw_cells usegs m' (0x77c00 - 164) [C4 errv] /\
lh_open usegs U4F m' t tbl size (firstn jf es) svs' /\ HEAPx A' (lh_blocks t tbl size (firstn jf es) ++ LB) m' md'.

Definition u_lh_delete_tail_stmt2 : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS U4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv) (jf : nat) (ef : lent),
HEAPx A (lh_blocks t tbl size es ++ LB) m md ->
lh_open usegs U4F m t tbl size es svs ->
nth_error es jf = Some ef -> (forall j x, (jf <= j)%nat -> nth_error es j = Some x -> le_v x = 0) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
rw_cells usegs m (0x77c00 - 164) [C4 errv] -> tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
(forall ms' md', u_lh_delete_tail_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv t tbl size es jf ms' md' ->
realizes usegs (mkCfg ms' md') T) ->
realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x28ab4) fc None m (seg_rom usegs)) md) T.
End U.

End RC__1.
