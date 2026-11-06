(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Walk.
Variable P : acc -> Prop.

Definition rzs2log_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo k : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].
Ltac lit_pow := repeat match goal with |- context [Z_to_bv 64 (16 * 2 ^ ?k)] => let v := eval vm_compute in (16 * 2 ^ k) in change (16 * 2 ^ k) with v end.

Lemma rzs2log_walk :
  forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x31000 -> P (Z_to_bv 64 a, n)) ->      (* [comment removed for export] *)
  0 <= k <= 7 -> a0 = Z_to_bv 64 (16 * 2^k) ->
  evtA asegs P (rzs2log_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38168) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros ST LOC LO SPH MI PSTK PRO Hk ->.
  aceil.
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  assert (CASES : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  carve_frame 16%nat ST.
  destruct CASES as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; lit_pow.
  all: do 32 cstep.
  all: release_frame FR ST (bv_unsigned sp); finishA.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition try_init_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma try_init_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)] ->                                             (* [comment removed for export] *)
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->    (* [comment removed for export] *)
  evtA asegs P (try_init_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5b0a0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros ST LOC LO SPH MI GI PSTK PDAT.
  aceil.
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  do 13 cstep.
  release_frame FR ST (bv_unsigned sp). finishA.
Qed.

Definition gmcs_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (ret_pc ra) fc None m (seg_rom asegs).

Lemma gmcs_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z),
  mem_inv asegs m -> 0 <= v < 2^31 ->
  rw_cells asegs m 0xae87c [C4 (Z_to_bv 64 v)] ->                                            (* [comment removed for export] *)
  (forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (gmcs_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5be28) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until v. intros MI Hv GM PDAT.
  do 4 cstep. apply evtA_done. unfold gmcs_post.
  replace (sx32 (Z_to_bv 64 v)) with (Z_to_bv 64 v); [reflexivity|].
  unfold sx32. rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition thread_cells (m : mem) (tp : word) (TSD CTX T : Z) : Prop :=
  rw_cells asegs m 0xad3e0 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xad3e4 [C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD)]
  /\ rw_cells asegs m TSD [C8 (Z_to_bv 64 CTX)]
  /\ rw_cells asegs m (CTX + 152) [C8 (Z_to_bv 64 T)].

Definition gct_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma get_current_thread_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo TSD CTX T : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  thread_cells m tp TSD CTX T -> 0xa4000 <= TSD -> TSD + 8 <= 0x603000 -> 0 < CTX -> CTX + 4096 <= alloc_ceiling -> 0 <= T < 2^47 ->
  0xa4000 + 88 <= bv_unsigned tp < 0x603000 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) ->
  evtA asegs P (gct_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d8a0) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until T. intros ST LOC LO SPH MI (G1 & G2 & G3 & G4 & G5) HT1 HT2 HC1 HC2 HT HTP PSTK PDAT P3.
  aceil.
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  do 3 cstep.           (* [comment removed for export] *)
  do 5 cstep.           (* [comment removed for export] *)
  cstep.                (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  cstep. cstep.          (* [comment removed for export] *)
  cstep. cstep. cstep.   (* [comment removed for export] *)
  cstep. cstep.          (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K. { exfalso. lia. }
  do 4 cstep.            (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finishA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z) : machine_state -> Prop :=
  fun ms' => exists a1 : word,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma asan_inited_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m -> rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)] ->
  (forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a190) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros MI GI PDAT. do 6 cstep. apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma getpc_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m ->
  evtA asegs P (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 ra a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x748e8) fc None m (seg_rom asegs)).
Proof. aceil. intros until m. intros MI. do 2 cstep. apply evtA_done. reflexivity. Qed.

End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Z_to_le_bytes_app : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof. aceil.
  induction n as [|n IH]; intros k z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH. f_equal. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma c8_c4c4 : forall v w, 0 <= v < 2^32 -> 0 <= w < 2^32 ->
  cells_bytes [C8 (Z_to_bv 64 (v + 2^32 * w))] = cells_bytes [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 w)].
Proof. aceil.
  intros v w Hv Hw. cbn [cells_bytes cbytes app]. rewrite app_nil_r. unfold le8, le4, word_to_le_bytes.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite !(Z.mod_small _ (2^64)) by lia.
  change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app. f_equal.
  - rewrite <- (Z_to_le_bytes_mod 4 (v + 2^32 * w) 32) by (cbn; lia). f_equal.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite app_nil_r. f_equal. rewrite Z.shiftr_div_pow2 by lia. replace (8 * Z.of_nat 4) with 32 by reflexivity.
    replace (2 ^ 32 * w) with (w * 2 ^ 32) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
End RC__1.
