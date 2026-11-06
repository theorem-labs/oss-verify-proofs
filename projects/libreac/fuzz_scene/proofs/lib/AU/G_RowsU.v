(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the glue's rows stack_malloc_8_sz / ASF8 / ASH00 / ASHF8 (AU/G_Top.v, Section g) at the
   concrete B := YD2l.TfibB, HB := YD2l.TfibB_syms, asan-ubsan image. The four proofs are a Theorem Labs lane's
   (at a423d9a58b9, lib/AU/ZZ_GlueRowsU.v, ZZ_GlueRowsU.v (sha256 82be105f2097; internal record)),
   renamed into the glue with this header; the lemma statements and proofs are unchanged. Each lemma has exactly the
   type of the row it closes. Rule 24: no function is walked here; each lemma applies an owner's discharge:
   - p_stack_malloc_8_sz: AU/Rt/StackMalloc8Closed.v stack_malloc_8_sz_discharged, with its start-up premises from
     SceneBCertU.v;
   - p_ASF8: AU/Rt/StackFree8Closed.v stack_free_8_discharged;
   - p_ASH00 / p_ASHF8: AU/RT_set_shadow.v scene_set_shadow_00 / scene_set_shadow_f8. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
  YK11 YK15 YK18 YK0c YK0e YG0f YG00 YG01 YG0n YG0d YG05 YG0q YG0t YK04 YA0i YA0n YI16
  YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import
  PaTable PaSym SceneSyms SceneList SceneCode ScenePa SceneImg ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YF0m SceneBCertU YD2l.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require StackMalloc8Closed StackFree8Closed StackFree8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require RT_set_shadow.
Import ListNotations.
Open Scope Z_scope.
(* The rows' notations, as AU/G_Close.v writes them. *)
#[local] Abbreviation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Abbreviation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation B := YD2l.TfibB (only parsing).
#[local] Notation HB := YD2l.TfibB_syms (only parsing).

(* The row stack_malloc_8_sz. *)
Lemma p_stack_malloc_8_sz : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  astack_malloc_sz_realizes SEGS B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8.
Proof.
  intros rc fx.
  refine (StackMalloc8Closed.stack_malloc_8_sz_discharged B (SceneBCertU.scene_LAWS B _) HB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - rewrite (SceneBCertU.scene_tp B HB). vm_compute. reflexivity.
  - rewrite (SceneBCertU.scene_tsd B HB). vm_compute. reflexivity.
  - exact (SceneBCertU.scene_c_fake_stack B HB).
  - exact (SceneBCertU.scene_c_tsd_slot B HB).
  - exact (SceneBCertU.scene_c_dtv B HB).
  - exact (SceneBCertU.scene_c_dtls B HB).
  - exact (SceneBCertU.scene_c_dtls_dtv1 B HB).
  - exact (SceneBCertU.scene_c_tsd_main B HB).
  - exact (SceneBCertU.scene_c_ctx_thread B HB).
  - exact (SceneBCertU.scene_c_thread_tls_beg B HB).
  - exact (SceneBCertU.scene_c_thread_tls_end B HB).
  - exact (SceneBCertU.scene_c_tls_got_mod B HB).
  - exact (SceneBCertU.scene_c_tls_got_off B HB).
  - exact (SceneBCertU.scene_c_real_tga B HB).
  - exact (SceneBCertU.scene_c_dtv1 B HB).
  - exact (SceneBCertU.scene_asan_inited_cell B HB).
  - exact (SceneBCertU.scene_c_tsd_key_inited B HB).
  - exact (SceneBCertU.scene_c_tsd_key B HB).
  - exact (SceneBCertU.scene_c_got_cflags B HB).
  - exact (SceneBCertU.scene_c_cflag_tga B HB).
  - exact (SceneBCertU.scene_c_got_verb B HB).
  - exact (SceneBCertU.scene_c_verb B HB).
  - exact (SceneBCertU.scene_c_got_dtls B HB).
Qed.

(* The row ASF8. *)
Lemma p_ASF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8.
Proof.
  intros rc fx.
  exact (StackFree8Closed.stack_free_8_discharged B (SceneBCertU.scene_LAWS B _) HB).
Qed.

(* The row ASH00. *)
Lemma p_ASH00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Proof.
  intros rc fx.
  exact (RT_set_shadow.scene_set_shadow_00 B (SceneBCertU.scene_LAWS B _) HB).
Qed.

(* The row ASHF8. *)
Lemma p_ASHF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Proof.
  intros rc fx.
  exact (RT_set_shadow.scene_set_shadow_f8 B (SceneBCertU.scene_LAWS B _) HB).
Qed.
