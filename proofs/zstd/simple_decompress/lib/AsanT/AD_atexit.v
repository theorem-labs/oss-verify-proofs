(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg F_syscalls MonadF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StrwF SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition ATX_SLOT : Z := 0x622d08.
Definition ATX_F1 : Z := 0x622d28.
Definition ATX_A1 : Z := 0x622e28.
Definition ATX_CALL : Z := 0xb6dd0.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo func : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x622d08, 0x622d0c); (0x622d28, 0x622d30); (0x622e28, 0x622e30)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x622d08 [C4 (Z_to_bv 64 2)]
    /\ rw_cells bsegs m' 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)]
    /\ rw_cells bsegs m' 0x622e28 [C8 (Z_to_bv 64 func)].

(* [comment removed for export] *)
Lemma atexit_reg1_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo func : Z) (f1 a1v : word) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  mem_inv bsegs m ->
  rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells bsegs m 0x622d00 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells bsegs m 0x622d04 [C4 (Z_to_bv 64 0)] ->                                  (* [comment removed for export] *)
  rw_cells bsegs m 0x622d08 [C4 (Z_to_bv 64 1)] ->                                  (* [comment removed for export] *)
  rw_cells bsegs m 0x622d10 [C8 (Z_to_bv 64 0x622d18)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x622d28 [C8 f1] ->                                              (* [comment removed for export] *)
  rw_cells bsegs m 0x622e28 [C8 a1v] ->                                             (* [comment removed for export] *)
  a0 = Z_to_bv 64 func -> (0 <= func < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z -> (bv_unsigned sp < 2^47)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb6d0c) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST MI LIBC FIN ALK SLOT HEAD F1 A1 -> FR LO KH SP47 RSTK RIMG.
  pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x622d08, 0x622d0c); (0x622d28, 0x622d30); (0x622e28, 0x622e30)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  do 12 hstep.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  (* [comment removed for export] *)
  hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). hstep. astep.
  (* [comment removed for export] *)
  hstep. astep.
  (* [comment removed for export] *)
  hstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity). hstep. astep.
  (* [comment removed for export] *)
  hstep. hstep. hstep. hstep. hstep. hstep.
  hstep. hstep. hstep.
  (* [comment removed for export] *)
  hstep. hstep. hstep. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). astep. hstep.
  (* [comment removed for export] *)
  do 8 hstep.
  release_frame FR0 ST (bv_unsigned sp).
  unfold atexit_post. finish.
Qed.
End CANSEC1.
