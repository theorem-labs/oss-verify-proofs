(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit AIcptU_hmap AIcptU_mem0.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac iprem0 :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- @eq word _ _ => reflexivity
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH in *; lia] end ]
  | |- rng_aimg _ => assumption
  | |- _ => unfold KHIGH in *; first [assumption | lia]
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition fwrite0_musl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fa : Z) (flags mode : word) (wend wpos wbase wfn buf bufsize fd lbf : Z) (tail : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fl' md' : word) (wend' wpos' wbase' : Z) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 256, bv_unsigned sp); (Fa, Fa + 232)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fa (file_cells fl' wend' wpos' wbase' wfn buf bufsize fd md' lbf tail)
    /\ (   (Z.land wend 18446744073709551615 <> 0 /\ fl' = flags /\ md' = mode /\ wend' = wend /\ wpos' = wpos /\ wbase' = wbase)      (* [comment removed for export] *)
        \/ (Z.land wend 18446744073709551615 = 0 /\ fl' = flags /\ wend' = buf + bufsize /\ wpos' = buf /\ wbase' = buf)                (* [comment removed for export] *)
        \/ (Z.land wend 18446744073709551615 = 0 /\ Z.land (bv_unsigned (zx32 flags)) 8 <> 0                                           (* [comment removed for export] *)
            /\ wend' = wend /\ wpos' = wpos /\ wbase' = wbase)).

Lemma fwrite0_musl_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo Fa : Z) (flags mode : word) (wend wpos wbase wfn buf bufsize fd lbf : Z) (tail : list byte),
  (Fa = RSTDOUT \/ Fa = RSTDERR) ->
  rw_cells asegs m Fa (file_cells flags wend wpos wbase wfn buf bufsize fd mode lbf tail) ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 256 -> KHIGH <= lo ->
  rt_got_ric m -> rt_inited m -> rt_real_mem m ->
  a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fa ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fwrite0_musl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fa flags mode wend wpos wbase wfn buf bufsize fd lbf tail m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1501f4) fc None m (seg_rom asegs)).
Proof.
  intros until tail. intros HF FC MI ST LO KLO RIC INI REAL -> -> ->. intros RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (Fa, Fa + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  unfold file_cells in FC.
  destruct HF as [-> | ->].
  all: carve_frame 64%nat ST.
  all: run_to 0x1500bc%Z.
  all: carve_frame 64%nat ST.
  all: do 12 astep.
  all: run_to 0x1501bc%Z.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 1376700) _ _ _ _) => zstep; call_sp (memcpy_i0_spec RNG)
       | |- _ => idtac
       end.
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ => iprem0 end.
  all: run_to 0%Z.
  all: match goal with H : rw_cells _ _ (bv_unsigned ?spv + -128) _, S : stk _ _ _ _ |- _ => release_frame H S (bv_unsigned spv + -64) end.
  all: match goal with H : rw_cells _ _ (bv_unsigned ?spv + -64) _, S : stk _ _ _ _ |- _ => release_frame H S (bv_unsigned spv) end.
  all: apply evtF_done; unfold fwrite0_musl_post, file_cells.
  all: do 19 eexists; eexists.
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|].
  all: split; [eassumption|].
  all: first [ left; repeat split; first [assumption | reflexivity]
             | right; left; repeat split; first [assumption | reflexivity]
             | right; right; repeat split; first [assumption | reflexivity] ].
Qed.
End CANSEC1.
