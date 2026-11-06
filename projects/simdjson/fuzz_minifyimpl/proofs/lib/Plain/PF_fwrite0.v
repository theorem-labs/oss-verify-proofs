(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import STRW_tac Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls StdioFiles Stdio_kit F_memcpy PExitU_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (a0 : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma memcpy0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  a2 = Z_to_bv 64 0 -> mem_inv psegs m ->
  evt psegs (memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc4398) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros -> MI.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  eapply evt_mono.
  - eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [] []).
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn in Hi. lia.
    + reflexivity.
    + change (Z.to_nat (bv_unsigned (Z_to_bv 64 0))) with 0%nat. split.
      * split; [cbn; split; [reflexivity| exact I]|]. cbn [cells_bytes cbytes app length]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn in Hi. lia.
      * split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
    + exact MI.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & _).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [| split; [exact WM| exact MI']].
    intros x _. apply MU. cbn [outside]. change (bv_unsigned (Z_to_bv 64 0)) with 0. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac iprem0 :=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- @eq word _ _ => reflexivity
  | |- _ => unfold GLOBALS_TOP in *; first [assumption | lia]
  end.

Definition fwrite0_musl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fa : Z) (flags mode : word) (wend wpos wbase wfn buf bufsize fd lbf : Z) (tail : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fl' md' : word) (wend' wpos' wbase' : Z) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 256, bv_unsigned sp); (Fa, Fa + 232)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' Fa (file_cells fl' wend' wpos' wbase' wfn buf bufsize fd md' lbf tail)
    /\ (   (Z.land wend 18446744073709551615 <> 0 /\ fl' = flags /\ md' = mode /\ wend' = wend /\ wpos' = wpos /\ wbase' = wbase)      (* [comment removed for export] *)
        \/ (Z.land wend 18446744073709551615 = 0 /\ fl' = flags /\ wend' = buf + bufsize /\ wpos' = buf /\ wbase' = buf)                (* [comment removed for export] *)
        \/ (Z.land wend 18446744073709551615 = 0 /\ Z.land (bv_unsigned (zx32 flags)) 8 <> 0                                           (* [comment removed for export] *)
            /\ wend' = wend /\ wpos' = wpos /\ wbase' = wbase)).

Lemma fwrite0_musl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo Fa : Z) (flags mode : word) (wend wpos wbase wfn buf bufsize fd lbf : Z) (tail : list byte),
  (Fa = RSTDOUT \/ Fa = RSTDERR) ->
  rw_cells psegs m Fa (file_cells flags wend wpos wbase wfn buf bufsize fd mode lbf tail) ->
  mem_inv psegs m -> stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 256 -> GLOBALS_TOP <= lo ->
  a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fa ->
  evt psegs (fwrite0_musl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa flags mode wend wpos wbase wfn buf bufsize fd lbf tail m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb9394) fc None m (seg_rom psegs)).
Proof.
  intros until tail. intros HF FC MI ST LO KLO -> -> ->.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (Fa, Fa + 232)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold GLOBALS_TOP in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  unfold file_cells in FC.
  destruct HF as [-> | ->].
  all: carve_frame 64%nat ST.
  all: run_to 0xb925c%Z.
  all: carve_frame 64%nat ST.
  all: do 12 xastep.
  all: run_to 0xb935c%Z.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 758620) _ _ _ _) => zstep; call_sp memcpy0_spec
       | |- _ => idtac
       end.
  all: lazymatch goal with |- evt _ _ _ => idtac | |- _ => iprem0 end.
  all: run_to 0%Z.
  all: match goal with H : rw_cells _ _ (bv_unsigned ?spv + -128) _, S : stk _ _ _ _ |- _ => release_frame H S (bv_unsigned spv + -64) end.
  all: match goal with H : rw_cells _ _ (bv_unsigned ?spv + -64) _, S : stk _ _ _ _ |- _ => release_frame H S (bv_unsigned spv) end.
  all: apply evt_done; unfold fwrite0_musl_post, file_cells.
  all: do 19 eexists; eexists.
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|].
  all: split; [eassumption|].
  all: first [ left; repeat split; first [assumption | reflexivity]
             | right; left; repeat split; first [assumption | reflexivity]
             | right; right; repeat split; first [assumption | reflexivity] ].
Qed.
