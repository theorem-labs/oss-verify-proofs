(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image SysStep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Stdio Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Exit Imp_ios_defs Pj_loc_defs Stdio_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).

Definition REXIT : Z := 0xb9844.
Definition EXIT_DEPTH : Z := 8448.
Definition RTPLOC : Z := 0xe9d68.
Definition RGLOC : Z := 0x10a060.
Definition ROFL : Z := 0x10a560.

Definition iosx_img_facts (m : mem) : Prop :=
  rw_cells psegs m 0xd3cb8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xd3dd8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xd4160 [C8 (Z_to_bv 64 0x7bfa0)]
  /\ rw_cells psegs m 0xd4290 [C8 (Z_to_bv 64 0x7c704)]
  /\ rw_cells psegs m 0xd4520 [C8 (Z_to_bv 64 0xa40b0)]
  /\ rw_cells psegs m 0xd47d0 [C8 (Z_to_bv 64 0xa38e4)].
Definition iosx_img_addr (a : Z) : Prop :=
  (0xd3cb8 <= a < 0xd3cc0) \/ (0xd3dd8 <= a < 0xd3de0) \/ (0xd4160 <= a < 0xd4168) \/ (0xd4290 <= a < 0xd4298) \/ (0xd4520 <= a < 0xd4528) \/ (0xd47d0 <= a < 0xd47d8).
Lemma iosx_img_facts_agree : forall P m m', agree_on' P m m' -> (forall a, iosx_img_addr a -> P a) -> iosx_img_facts m -> iosx_img_facts m'.
Proof.
  intros P m m' AG HP (H1 & H2 & H3 & H4 & H5 & H6). unfold iosx_img_addr in HP.
  Ltac tr1 AG HP H := eapply rw_cells_agree'; [exact AG| exact H|]; intros a Ha; apply HP; cbn in Ha; lia.
  split; [tr1 AG HP H1|]. split; [tr1 AG HP H2|]. split; [tr1 AG HP H3|]. split; [tr1 AG HP H4|]. split; [tr1 AG HP H5| tr1 AG HP H6].
Qed.

Definition XW (sp : Z) : list (Z * Z) :=
  [(0x10b000, sp); (0, 0xd0000); (0x10a028, 0x10a028 + 112); (0xe9cf4, 0xe9cf8); (0x10a008, 0x10a010); (0xd66b0, 0xd66b8); (0x10a1a0, 0x10a1a8 + 928);
   (0xd7990, 0xd7990 + 232); (0x10a988, 0x10a988 + 1024); (0xd77b0, 0xd77b0 + 232); (RTPLOC, RTPLOC + 8); (AEX_VEC_OBJ + 8, AEX_VEC_OBJ + 24)].
Definition xagree (sp : Z) (m m' : mem) : Prop := agree_on' (fun a => outside (XW sp) a) m m'.

Lemma xagree_refl : forall sp m, xagree sp m m.
Proof. intros sp m a _ _. auto. Qed.
Lemma xagree_trans : forall sp m1 m2 m3, xagree sp m1 m2 -> xagree sp m2 m3 -> xagree sp m1 m3.
Proof. intros sp m1 m2 m3 H1 H2 a Ha Ho. destruct (H1 a Ha Ho) as [E1 W1]. destruct (H2 a Ha Ho) as [E2 W2]. split; [congruence| auto]. Qed.
Lemma xagree_of_munch : forall sp W m m', munch W m m' -> wmono psegs m m' -> (forall a, outside (XW sp) a -> outside W a) -> xagree sp m m'.
Proof. intros sp W m m' MU WM HW a Ha Ho. apply (agree_on'_of_munch W m m' MU WM a Ha). apply HW. exact Ho. Qed.
Lemma xagree_mono_sp : forall sp sp' m m', xagree sp m m' -> sp <= sp' -> xagree sp' m m'.
Proof. intros sp sp' m m' H LE a Ha Ho. apply H; [exact Ha|]. unfold XW in *. cbn [outside fst snd] in *. lia. Qed.

Section WithCeiling. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition xheap (s : PState) (m : mem) (LB : list block) (x : option bptr) (k : Z) (SP : Z) (tp : word) : Prop :=
  match x with
  | None => k = 0
  | Some p => k = 1 /\ RHEAP s LB m /\ (exists B, rauxv_ok m B /\ SP <= B < 2^63) /\ (exists errv : word, rw_cells psegs m (errno_addr tp) [C4 errv])
              /\ exists (A : Z), In (p, A, 8) LB /\ rw_cells psegs m AEX_VEC_OBJ [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 8)); C8 (Z_to_bv 64 (A + 8))] /\ 0 < A
  end.

Definition at_exit_immp (x : option bptr) (code : Z) (s : PState) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word) (k : Z) (LB : list block),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REXIT) fc None m (seg_rom psegs)

    /\ stk psegs m lo (bv_unsigned sp) /\ (lo <= bv_unsigned sp - EXIT_DEPTH) /\ (alloc_ceiling <= lo) /\ (GLOBALS_TOP <= lo)

    /\ rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]

    /\ rw_cells psegs m 0x10a000 [C4 z64]
    /\ rw_cells psegs m 0xd66b8 [C8 (Z_to_bv 64 0xd0608); C8 (Z_to_bv 64 0xd0600)]
    /\ rw_cells psegs m 0xd0600 [C8 (Z_to_bv 64 0x3e670)]
    /\ rw_cells psegs m 0xd7ae8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0xd64f8 [C8 (Z_to_bv 64 0xb9660); C8 z64]
    /\ rw_cells psegs m 0xd76e0 [C8 (Z_to_bv 64 0xd76e0)]
    /\ rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ aex_cells m k /\ (0 <= k <= 1)

    /\ rw_cells psegs m ROFL [C4 z64; C4 z64; C8 z64]
    /\ rw_cells psegs m 0xd7988 [C8 (Z_to_bv 64 RSTDIN)] /\ stdin_file0 m
    /\ rw_cells psegs m 0xd7a78 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0xd7898 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_wfile0 m
    /\ ssp_cells m guard

    /\ LOCB m /\ imp_ios m /\ rw_cells psegs m RTPLOC [C8 (Z_to_bv 64 RGLOC)] /\ iosx_img_facts m

    /\ xheap s m LB x k (bv_unsigned sp) tp
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code /\ (0 <= code < 2^64)
    /\ (0 < t < 4194304).

Definition at_exit_imp (code : Z) (s : PState) (ms : machine_state) : Prop := at_exit_immp (ps_x s) code s ms.

Lemma at_exit_imp_of_immp : forall x code s ms, at_exit_immp x code s ms -> ps_x s = x -> at_exit_imp code s ms.
Proof. intros x code s ms H <-. exact H. Qed.

End WithCeiling.
