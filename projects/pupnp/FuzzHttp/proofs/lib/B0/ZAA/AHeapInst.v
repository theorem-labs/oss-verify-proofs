(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv ASec AQuar AHeap ALedger AHeap2 ALinkPg ALinkVm ALink AVaOf AHeapLaws.
Import ListNotations.
Open Scope Z_scope.

Section INST.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv) (FI : fs_if) (Bs : vmbase).
Hypothesis AO : alayout_ok AL.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis SP0S : alloc_ceiling + 2^23 + 184 <= 2^47.

Hypothesis FSEI : forall m, thread_env (al_thread AL) m -> AFsEnv.fs_tls_env (at_thr (al_thread AL)) AFsEnv.A0_DTV AFsEnv.A0_TLSB (al_dtls AL) (al_fsb AL) m -> FSENV FI m.

Definition AI_B : am_if FI :=
  mkAM FI Z Z.eqb Z.eqb_eq astB bs_ghost (fun s vm => LINKvm Bs (va_of s) vm) bs_nsec (RHEAP_B AL E) a0_static
       (at_top (al_thread AL)) (at_bottom (al_thread AL))
       (law_stack_ok AL AO)
       SP0S
       (law_block_range AL E AO FI FSBE)
       (law_blocks_disjoint AL E AO)
       (law_blocks_nodup AL E AO)
       (law_block_slack AL E AO FI FSBE)
       (law_block_shadow AL E)
       (law_block_shread AL E AO FI FSBE)
       (law_heap_frame AL E AO FI FSBE)
       (law_heap_perm AL E)
       (law_fsenv AL E FI FSEI).

#[using="Type"] Lemma AI_B_static : forall lo hi, am_static FI AI_B lo hi <-> a0_static lo hi.
Proof. intros lo hi. reflexivity. Qed.
#[using="Type"] Lemma AI_B_ghost : forall s, am_ghost FI AI_B s = (bs_H s, bs_pages s). Proof. reflexivity. Qed.
#[using="Type"] Lemma AI_B_nsec : forall s, am_nsec FI AI_B s = bs_nsec s. Proof. reflexivity. Qed.
#[using="Type"] Lemma AI_B_heap : forall s LB m, RHEAP_A FI AI_B s LB m = RHEAP_B AL E s LB m. Proof. reflexivity. Qed.
End INST.
