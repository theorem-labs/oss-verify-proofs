(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv AInitReps AFsEnv AFakeRep AFakeInst AFakeInit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueIcpt GlueAllocKit GlueAllocLay.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section Fs.
Context {HC : HasCeiling}.
Variable V : nat -> Z.
Hypothesis AO : alayout_ok (AL_of V).
Variable m : mem.
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.

#[using="AO HM"] Lemma fs_tls_env_init : fs_tls_env (at_thr (al_thread (AL_of V))) A0_DTV A0_TLSB (al_dtls (AL_of V)) (al_fsb (AL_of V)) m.
Proof.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (dtls_region_B (AL_of V) AO) as (DR1 & DR2 & DR3). cbn [fst snd] in DR1, DR2, DR3.
  unfold fs_tls_env, AL_of in *. cbn [al_thread at_thr al_dtls al_fsb] in *.
  split. { lcells V m HM 0xabeb8 [C8 (wz 0xa3130)] H. exact H. }
  split. { lcells V m HM 0xaadc0 [C8 (wz 1); C8 (wz 18446744073709549568); C8 (wz 8)] H. exact H. }
  split. { lcells V m HM 6187368 [C8 (wz A0_DTV)] H. exact H. }
  split. { lcells V m HM 6187416 [C8 (wz A0_TLSB)] H. exact H. }
  split. { mf V m HM (MCell (ZLit 6187376) 8 (ZMul (ZLit 4096) (ZV 377))) H. exact H. }
  split. { lcells V m HM 0x1454b1 [C1 (Z_to_bv 8 1)] H. exact H. }
  split. { lcells V m HM 0xaa120 [C8 (wz 0x143398)] H. exact H. }
  split. { lcells V m HM 0x143398 [C4 (wz 0)] H. exact H. }
  split. { mf V m HM (MCell (ZLit 6187384) 8 (ZMul (ZLit 4096) (ZV 310))) H. exact H. }
  split. { exists 6187376. split; [| lia]. mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6187376)) H. exact H. }
  split. { exists (wz 6189224), (wz 6189444).
           mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6189224)) H1.
           mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6189444)) H2.
           apply (proj2 (rw_cells_app asegs m _ [_] [_])). split; [exact H1|]. cbn [cells_size csize Nat.add].
           replace (4096 * V 227%nat + 48 + Z.of_nat 8) with (4096 * V 227%nat + 56) by lia. exact H2. }
  repeat split; lia.
Qed.

#[using="HC AO HM"] Lemma RFAKE_init : RFAKE_B (al_fsb (AL_of V)) fst0 m.
Proof.
  pose proof (fsb_ok_B (AL_of V) AO) as FOK. pose proof FOK as (F1 & F2 & F3 & F4 & F5).
  unfold AL_of in F1, F2, F3, F4, F5. cbn [al_fsb] in F1, F2, F3, F4, F5.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 377)) 11571200) W0.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 96)) 11571104) ZR.
  mf V m HM (MWr (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400) WS.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400) ZS.
  apply (RFAKE_B_init (al_fsb (AL_of V)) FOK m (repeat (Z_to_bv 8 0) (Z.to_nat A0_FS_SHSIZE))); unfold AL_of; cbn [al_fsb].
  - mf V m HM (MZeroC (ZMul (ZLit 4096) (ZV 377)) 88) H. exact H.
  - mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 88)) 8 (ZLit 20)) H. exact H.
  - apply (zero_run m _ _ 11571104 _ 11571200 ZR W0 0 (A0_FS_SIZE - 96)); lia.
  - apply (zero_run m _ _ 1446400 _ 1446400 ZS WS 0 A0_FS_SHSIZE); try lia.
    unfold sh, SHADOW_OFF. clear - F1. Z.div_mod_to_equations. lia.
    unfold sh, SHADOW_OFF. clear - F1. Z.div_mod_to_equations. lia.
    unfold sh, SHADOW_OFF. clear - F1. Z.div_mod_to_equations. lia.
    unfold sh, SHADOW_OFF. clear - F1. Z.div_mod_to_equations. lia.
Qed.
End Fs.
