(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout ACells LJ AFake AFakeRep AFsEnv.
Import ListNotations.
Open Scope Z_scope.

Section INST.
Context {HC : HasCeiling}.
Variable L : alayout.
Hypothesis AO : alayout_ok L.

#[using="AO"] Lemma fsb_ok_B : 0x609000 <= al_fsb L /\ al_fsb L + A0_FS_SIZE <= alloc_ceiling /\ app_mem (al_fsb L) A0_FS_SIZE /\ al_fsb L mod 4096 = 0
                 /\ (al_fsb L + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= al_fsb L).
Proof.
  layout_facts AO 4%nat RF. destruct RF as ((R1 & _) & R2 & R3 & R4 & R5 & R6 & _).
  split; [lia|]. split; [exact R2|]. split; [exact R6|]. split; [exact R3|]. lia.
Qed.

#[using="HC AO"] Lemma fsb_pos_B : 0 <= al_fsb L. Proof. pose proof fsb_ok_B as (B1 & _). lia. Qed.
#[using="HC AO"] Lemma fsb_mod_B : al_fsb L mod 4096 = 0. Proof. pose proof fsb_ok_B as (_ & _ & _ & B4 & _). exact B4. Qed.

#[using="AO"] Lemma dtls_region_B : region_ok (al_dtls L, 4096).
Proof. destruct AO as (F & _). exact (proj1 (Forall_nth region_ok (al_regions L)) F 7%nat (0, 0) ltac:(cbn; lia)). Qed.
#[using="HC AO"] Lemma dtls_fs_B : apart (al_dtls L) 4096 (al_fsb L) A0_FS_SIZE.
Proof. layout_apart_fact AO 4%nat 7%nat H. unfold apart. lia. Qed.

Definition FI_B : fs_if :=
  mkFS fstate (fst_live (al_fsb L)) (RFAKE_B (al_fsb L)) (fsenv_B L (al_dtls L)) (fst_malloc (al_fsb L)) fst_release (al_fsb L)
    fsb_ok_B
    (fun st m (R : RFAKE_B (al_fsb L) st m) => fst_live_wf (al_fsb L) fsb_pos_B fsb_mod_B st (proj1 R))
    (fun st m m' W R MU WM FA => rfake_B_frame (al_fsb L) fsb_ok_B st m m' W R MU WM FA)
    (fun st k m (R : RFAKE_B (al_fsb L) st m) Hk => fst_new_facts (al_fsb L) fsb_pos_B fsb_mod_B st k (proj1 R) Hk)
    (fun st ff rest m m' cs R LV MU WM F1 F2 F3 SZ => rfake_B_release (al_fsb L) fsb_ok_B st ff rest m m' cs R LV MU WM F1 F2 F3 SZ)
    (fun st m m' W R MU FA => rfake_B_frame_m (al_fsb L) fsb_ok_B st m m' W R MU FA)
    (fun st m m' W R MU WM FA => rfake_B_frame_g (al_fsb L) fsb_ok_B st m m' W R MU WM FA)
    (fun m m' W FE MU FA => fsenv_B_frame L (al_dtls L) AO dtls_region_B dtls_fs_B m m' W FE MU FA).
End INST.
