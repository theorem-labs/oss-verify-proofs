(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ogg_sync_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0 = wz 0
/\ sync_rep m' A 0 ogg_sync_init [].

Lemma ogg_sync_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (junk : list byte),
a0 = wz A -> 0 < A ->
rw_cells rsegs m A [CB 32 junk] ->
mem_inv rsegs m ->
evt rsegs (ogg_sync_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_init) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros -> Apos OBJ MI. unfold A_ogg_sync_init, wz.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add] in GB.
zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_wz in K by lia; lia|].
lstep. lstep. lstep. lstep. zstep. zstep.
finish. { reflexivity. }
split. { eapply rw_cells_recell; [exact OBJ| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity]. }
split. { unfold sync_fields_ok, int31; cbn. lia. }
split. { cbn. repeat split; reflexivity. }
cbn. lia.
Qed.

Definition ogg_sync_wrote_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A D : Z) (sy : sync_st bptr) (bytes : list byte) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0 = wz (fst (ogg_sync_wrote sy n))
/\ sync_rep m' A D (snd (ogg_sync_wrote sy n)) bytes.

Lemma ogg_sync_wrote_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A D : Z) (sy : sync_st bptr) (bytes : list byte) (n : Z),
a0 = wz A -> a1 = wz n -> 0 <= n -> sy_fill sy + n < 2^31 ->
sync_rep m A D sy bytes ->
mem_inv rsegs m ->
evt rsegs (ogg_sync_wrote_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A D sy bytes n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_wrote) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros -> -> Hn Hfit sfH_; first [ sf_destruct 4%nat sfH_ as OBJ FOK DAT SEP | sf_fb; destruct sfH_ as (OBJ & FOK & DAT & SEP) ]; intros MI. unfold A_ogg_sync_wrote, wz. unfold sync_cells, wz in OBJ.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add] in GB.

unfold sync_data in DAT.
destruct (sy_data sy) as [p|] eqn:ED;
[first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ] | first [ sf_destruct 4%nat DAT as D1 D2 D3 D4 | sf_fb; destruct DAT as (D1 & D2 & D3 & D4) ]].
all: zstep; zstep; rewrite sx32_lit by (unfold int31; lia); zstep; zstep.
all: if_cases K; zify_cond K; [exfalso; lia|].
all: zstep; rewrite sx32_lit by (unfold int31; lia); zstep; zstep.
all: if_cases K2; zify_cond K2; rewrite !signed_lit_small in K2 by lia.
Local Ltac post_tac sy n ED :=
unfold ogg_sync_wrote, ogg_sync_check; destruct (Z.ltb_spec (sy_storage sy) 0); [lia|];
destruct (Z.ltb_spec (sy_storage sy) (sy_fill sy + n)); try lia; cbn [fst snd];
unfold sync_rep, sync_data, sync_cells, wz; cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes];
rewrite ?ED.
- zstep. finish; post_tac sy n ED; [reflexivity|].
split; [exact OBJ|]. split; [exact FOK|]. split; [| exact SEP]. split; [exact D1|]. split; [exact ARR|]. auto.
- zstep. lstep. zstep. finish; post_tac sy n ED; [reflexivity|].
replace (sy_fill sy + n) with (n + sy_fill sy) by lia.
split; [exact OBJ|]. split; [unfold sync_fields_ok, int31 in *; cbn; lia|]. split; [| exact SEP].
split; [exact D1|]. split; [exact ARR|]. auto.
- zstep. finish; post_tac sy n ED; [reflexivity|].
split; [exact OBJ|]. split; [exact FOK|]. split; [| exact SEP]. auto.
- zstep. lstep. zstep. finish; post_tac sy n ED; [reflexivity|].
replace (sy_fill sy + n) with (n + sy_fill sy) by lia.
split; [exact OBJ|]. split; [unfold sync_fields_ok, int31 in *; cbn; lia|]. split; [| exact SEP]. auto.
Qed.

