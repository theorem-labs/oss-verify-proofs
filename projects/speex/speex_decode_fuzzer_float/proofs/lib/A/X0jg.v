(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0ec.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_sx32 :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) : list cell :=
[C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

Definition ph_slot (ph : bool) : Z := if ph then 2 else 1.

Definition atexit_ph1 (m : word -> option byte) : Prop :=
rw_cells bsegs m 0x658d10 [C8 (Z_to_bv 64 0xe6d8c)] /\ rw_cells bsegs m 0x658e10 [C8 (Z_to_bv 64 0x966dc)]
/\ rw_cells bsegs m 0x638114 [C1 (Z_to_bv 8 0)].

Definition atexit_ph (ph : bool) (m : word -> option byte) : Prop := if ph then atexit_ph1 m else True.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x658ce8, 0x658d00)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' 0x658ce8 (atexit_cells (Z_to_bv 8 1) p1 p2 32 0 0 0xe6d8c).

Lemma funcs_on_exit_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x658ce8 (atexit_cells fin p1 p2 1 0x658d00 0 0xe6d8c) ->
rw_cells bsegs m 0x658e08 [C8 (Z_to_bv 64 0x85d14)] ->
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells bsegs m 0x197960 [C1 (Z_to_bv 8 0)] ->
mem_inv bsegs m ->
lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6bfc) fc None m (seg_rom bsegs)).
Proof.
intros until tm1. intros ST ATX ATA LIBC COV MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x658ce8, 0x658d00)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xe6c78%Z.

xstep. xsteps_to 0xe6cc0%Z.
release_frame FR ST (bv_unsigned sp).

xstep. xsteps_to 0xf2254%Z. xstep.
unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x658ce8 (atexit_cells fin p1 p2 2 0x658d00 0 0xe6d8c) ->
rw_cells bsegs m 0x658e08 [C8 (Z_to_bv 64 0x85d14)] ->
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells bsegs m 0x197960 [C1 (Z_to_bv 8 0)] ->
atexit_ph1 m ->
mem_inv bsegs m ->
lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6bfc) fc None m (seg_rom bsegs)).
Proof.
intros until tm1. intros ST ATX ATA LIBC COV (F1 & A1 & FLAG) MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x658ce8, 0x658d00)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xe6c78%Z.
xstep. xsteps_to 0xe6c78%Z.
xstep. xsteps_to 0xe6cc0%Z.
release_frame FR ST (bv_unsigned sp).
xstep. xsteps_to 0xf2254%Z. xstep.
unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x658ce8 (atexit_cells fin p1 p2 (ph_slot ph) 0x658d00 0 0xe6d8c) ->
rw_cells bsegs m 0x658e08 [C8 (Z_to_bv 64 0x85d14)] ->
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells bsegs m 0x197960 [C1 (Z_to_bv 8 0)] ->
atexit_ph ph m ->
mem_inv bsegs m ->
lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6bfc) fc None m (seg_rom bsegs)).
Proof.
intros [|]; cbn [ph_slot atexit_ph]; intros.
- eapply funcs_on_exit_spec1; eassumption.
- eapply funcs_on_exit_spec0; eassumption.
Qed.

Definition TR_LATCH : Z := 0x638110.

Definition reg_pre (m : word -> option byte) : Prop :=
exists (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
rw_cells bsegs m 0x658ce8 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x658d00 0 0xe6d8c)
/\ rw_cells bsegs m 0x658d10 [C8 j1] /\ rw_cells bsegs m 0x658e10 [C8 j2]
/\ rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
/\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 0)].

Definition reg_post (m : word -> option byte) : Prop :=
exists (p1 p2 : list byte),
rw_cells bsegs m 0x658ce8 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x658d00 0 0xe6d8c)
/\ rw_cells bsegs m 0x658d10 [C8 (Z_to_bv 64 0xe6d8c)] /\ rw_cells bsegs m 0x658e10 [C8 (Z_to_bv 64 0x966dc)]
/\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 1)].

Definition REG_CELLS : list (Z * Z) := [(0x638110, 0x638111); (0x658ce8, 0x658d00); (0x658d10, 0x658d18); (0x658e10, 0x658e18)].

Lemma in_REG_CELLS : forall x, in_ranges REG_CELLS x <->
(0x638110 <= x < 0x638111 \/ 0x658ce8 <= x < 0x658d00 \/ 0x658d10 <= x < 0x658d18 \/ 0x658e10 <= x < 0x658e18).
Proof.
intros x. unfold REG_CELLS, in_ranges. split.
- intros (lo & hi & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- intros [H|[H|[H|H]]]; [exists 0x638110, 0x638111| exists 0x658ce8, 0x658d00| exists 0x658d10, 0x658d18| exists 0x658e10, 0x658e18];
(split; [cbn; tauto| exact H]).
Qed.

Definition atexit_reg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo func : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x658ce8, 0x658d00); (0x658d10, 0x658d18); (0x658e10, 0x658e18)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' 0x658ce8 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x658d00 0 0xe6d8c)
/\ rw_cells bsegs m' 0x658d10 [C8 (Z_to_bv 64 0xe6d8c)] /\ rw_cells bsegs m' 0x658e10 [C8 (Z_to_bv 64 func)].

Lemma atexit_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
a0 = Z_to_bv 64 func -> 0 <= func < 2^64 ->
stk bsegs m lo (bv_unsigned sp) ->
rw_cells bsegs m 0x658ce8 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x658d00 0 0xe6d8c) ->
rw_cells bsegs m 0x658d10 [C8 j1] -> rw_cells bsegs m 0x658e10 [C8 j2] ->
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv bsegs m ->
lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
evt bsegs (atexit_reg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe6cc8) fc None m (seg_rom bsegs)).
Proof.
intros until j2. intros -> HF ST ATX F1 A1 LIBC MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x658ce8, 0x658d00); (0x658d10, 0x658d18); (0x658e10, 0x658e18)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xe6d70%Z.
xstep. xstep. xstep. xstep. xstep.
release_frame FR ST (bv_unsigned sp).
xstep. xstep.
unfold atexit_reg_post, atexit_cells. sys_finish.
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_sx32 :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) : list cell :=
[C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

Definition ph_slot (ph : bool) : Z := if ph then 2 else 1.

Definition atexit_ph1 (m : word -> option byte) : Prop :=
rw_cells asegs m 0x6504d0 [C8 (Z_to_bv 64 0xde65c)] /\ rw_cells asegs m 0x6505d0 [C8 (Z_to_bv 64 0x965f0)]
/\ rw_cells asegs m 0x62f8d4 [C1 (Z_to_bv 8 0)].

Definition atexit_ph (ph : bool) (m : word -> option byte) : Prop := if ph then atexit_ph1 m else True.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6504a8, 0x6504c0)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' 0x6504a8 (atexit_cells (Z_to_bv 8 1) p1 p2 32 0 0 0xde65c).

Lemma funcs_on_exit_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6504a8 (atexit_cells fin p1 p2 1 0x6504c0 0 0xde65c) ->
rw_cells asegs m 0x6505c8 [C8 (Z_to_bv 64 0x85c28)] ->
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells asegs m 0x18f120 [C1 (Z_to_bv 8 0)] ->
mem_inv asegs m ->
lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde4cc) fc None m (seg_rom asegs)).
Proof.
intros until tm1. intros ST ATX ATA LIBC COV MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6504a8, 0x6504c0)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xde548%Z.

xstep. xsteps_to 0xde590%Z.
release_frame FR ST (bv_unsigned sp).

xstep. xsteps_to 0xe99e0%Z. xstep.
unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6504a8 (atexit_cells fin p1 p2 2 0x6504c0 0 0xde65c) ->
rw_cells asegs m 0x6505c8 [C8 (Z_to_bv 64 0x85c28)] ->
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells asegs m 0x18f120 [C1 (Z_to_bv 8 0)] ->
atexit_ph1 m ->
mem_inv asegs m ->
lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde4cc) fc None m (seg_rom asegs)).
Proof.
intros until tm1. intros ST ATX ATA LIBC COV (F1 & A1 & FLAG) MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6504a8, 0x6504c0)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xde548%Z.
xstep. xsteps_to 0xde548%Z.
xstep. xsteps_to 0xde590%Z.
release_frame FR ST (bv_unsigned sp).
xstep. xsteps_to 0xe99e0%Z. xstep.
unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6504a8 (atexit_cells fin p1 p2 (ph_slot ph) 0x6504c0 0 0xde65c) ->
rw_cells asegs m 0x6505c8 [C8 (Z_to_bv 64 0x85c28)] ->
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
ro_cells asegs m 0x18f120 [C1 (Z_to_bv 8 0)] ->
atexit_ph ph m ->
mem_inv asegs m ->
lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde4cc) fc None m (seg_rom asegs)).
Proof.
intros [|]; cbn [ph_slot atexit_ph]; intros.
- eapply funcs_on_exit_spec1; eassumption.
- eapply funcs_on_exit_spec0; eassumption.
Qed.

Definition TR_LATCH : Z := 0x62f8d0.

Definition reg_pre (m : word -> option byte) : Prop :=
exists (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
rw_cells asegs m 0x6504a8 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x6504c0 0 0xde65c)
/\ rw_cells asegs m 0x6504d0 [C8 j1] /\ rw_cells asegs m 0x6505d0 [C8 j2]
/\ rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
/\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 0)].

Definition reg_post (m : word -> option byte) : Prop :=
exists (p1 p2 : list byte),
rw_cells asegs m 0x6504a8 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x6504c0 0 0xde65c)
/\ rw_cells asegs m 0x6504d0 [C8 (Z_to_bv 64 0xde65c)] /\ rw_cells asegs m 0x6505d0 [C8 (Z_to_bv 64 0x965f0)]
/\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 1)].

Definition REG_CELLS : list (Z * Z) := [(0x62f8d0, 0x62f8d1); (0x6504a8, 0x6504c0); (0x6504d0, 0x6504d8); (0x6505d0, 0x6505d8)].

Lemma in_REG_CELLS : forall x, in_ranges REG_CELLS x <->
(0x62f8d0 <= x < 0x62f8d1 \/ 0x6504a8 <= x < 0x6504c0 \/ 0x6504d0 <= x < 0x6504d8 \/ 0x6505d0 <= x < 0x6505d8).
Proof.
intros x. unfold REG_CELLS, in_ranges. split.
- intros (lo & hi & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- intros [H|[H|[H|H]]]; [exists 0x62f8d0, 0x62f8d1| exists 0x6504a8, 0x6504c0| exists 0x6504d0, 0x6504d8| exists 0x6505d0, 0x6505d8];
(split; [cbn; tauto| exact H]).
Qed.

Definition atexit_reg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo func : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6504a8, 0x6504c0); (0x6504d0, 0x6504d8); (0x6505d0, 0x6505d8)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' 0x6504a8 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x6504c0 0 0xde65c)
/\ rw_cells asegs m' 0x6504d0 [C8 (Z_to_bv 64 0xde65c)] /\ rw_cells asegs m' 0x6505d0 [C8 (Z_to_bv 64 func)].

Lemma atexit_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
a0 = Z_to_bv 64 func -> 0 <= func < 2^64 ->
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6504a8 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x6504c0 0 0xde65c) ->
rw_cells asegs m 0x6504d0 [C8 j1] -> rw_cells asegs m 0x6505d0 [C8 j2] ->
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv asegs m ->
lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
evt asegs (atexit_reg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func p1 p2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde598) fc None m (seg_rom asegs)).
Proof.
intros until j2. intros -> HF ST ATX F1 A1 LIBC MI LO LOLO.
unfold atexit_cells in ATX.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6504a8, 0x6504c0); (0x6504d0, 0x6504d8); (0x6505d0, 0x6505d8)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
xsteps_to 0xde640%Z.
xstep. xstep. xstep. xstep. xstep.
release_frame FR ST (bv_unsigned sp).
xstep. xstep.
unfold atexit_reg_post, atexit_cells. sys_finish.
Qed.
