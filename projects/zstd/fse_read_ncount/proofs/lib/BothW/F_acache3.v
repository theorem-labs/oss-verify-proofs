(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AModelFacts APrimFacts F_acache F_acache2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).
Section CANSEC1. Context {rc : runConstT}.
Definition cb_sm (s : Z) : Z :=
let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT}.
Definition cb_clz (y : Z) : Z :=
let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
* 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT}.
Definition cb_fin (s : Z) : Z :=
let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
+ Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
+ -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT}.
Definition cb_sm_ok (s : Z) : bool :=
negb (s mod 8 =? 0) || (let y := cb_sm s in let k := cb_clz y in (0 <=? y) && (y <? 2^64) && (47 <=? k) && (k <=? 54)).
#[using="Type"] Lemma cb_sm_ok_all : forallb_range cb_sm_ok 513 (Z.to_nat (65536 - 513 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Local Opaque cb_sm cb_clz.
Local Strategy expand [cb_sm_ok].
#[using="Type"] Lemma cb_sm_ok_sound : forall s, cb_sm_ok s = true -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
intros z Hz M8. unfold cb_sm_ok in Hz. cbv zeta in Hz. replace (z mod 8 =? 0) with true in Hz by (symmetry; apply Z.eqb_eq; exact M8). cbn [negb orb] in Hz.
rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
repeat split; assumption.
Qed.
#[using="Type"] Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
exact (range_by_compute (fun s => s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54) cb_sm_ok 513 65536 cb_sm_ok_sound cb_sm_ok_all).
Qed.
Local Transparent cb_sm cb_clz.
#[using="Type"] Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (size : Z),
513 <= size <= 65536 -> size mod 8 = 0 ->
rng_aimg RNG ->
evtF bsegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x369b0) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x368d4) fc None m (seg_rom bsegs)).
Proof.
intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>14937404945.5414939502106.5116083456451.5019620497065.522548589748.49 28913119920.5528913119921.5434887345831.4639649869104.5540834385896.4940834385897.4840834385898.4741408184392.4941408184393.4841408184394.4744007240617.4844007240618.4751255471498.5152525112624.5553508216720.5559586081462.4759588178608.5559588178609.5463375992104.4963375992105.4863375992106.4764344627643.5065096534932.5565096534933.5465098632080.4965098632081.4865098632082.4765098632094.5165104484284.4165510090920.4965510090921.4865510090922.476746801848.49 6746801849.48 6746801850.47 8937270822.47 8937270827.50 00000100200700800900:00;00<00=00>00?00@00A00B00C00D00E00I00J00K00L00M00N00O00P00Q00R00V00Z00^00b00f00j00n00o010011012013014015016FFS3CLZFSSSFSSSSSSSSSS2SZSSSSSSSSSS2SZS2SZS2SZS2SZS2SZS2SZS2SZSSSSSSFF".
do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).
do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).
do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).
setreg 8 (Z_to_bv 64 (class_id size))
ltac:(symmetry; revert M8; revert SZ; clear; revert size;
lazymatch goal with |- forall z, _ -> _ -> Z_to_bv 64 _ = Z_to_bv 64 _ => idtac | |- ?G => idtac "CB-GOAL" G end;
apply (range_bv_eq8 cb_fin class_id 513 65536); vm_cast_no_check (eq_refl true)).
apply evtF_done. do 7 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC4.
