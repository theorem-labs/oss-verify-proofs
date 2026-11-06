(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the glue's rows stack_malloc_8_sz / ASF8 / ASH00 / ASHF8 (A/G_Top.v, Section g) at the
   concrete B := AD2l.TfibB, HB := AD2l.TfibB_syms, asan image. The four proofs are a Theorem Labs lane's
   (at a423d9a58b9, lib/A/ZZ_GlueRows.v, ZZ_GlueRows.v (sha256 d621fde2e0cb; internal record)),
   renamed into the glue with this header; the lemma statements and proofs are unchanged. Each lemma has exactly the
   type of the row it closes. Rule 24: no function is walked here; each lemma applies an owner's discharge:
   - p_stack_malloc_8_sz: A/Rt/StackMalloc8Closed.v stack_malloc_8_sz_discharged, with its start-up premises from
     SceneBCert.v;
   - p_ASF8: A/Rt/StackFree8Closed.v stack_free_8_discharged;
   - p_ASH00 / p_ASHF8: A/RT_set_shadow.v scene_set_shadow_00 / scene_set_shadow_f8. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
  YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02
  YG0f YG00 YG01 YG0n YG0d YG05 YG0q YG0t YK04 YA0i YA0n YCbq YI16 YC5d YCbp
  YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
  PaTable PaSym SceneSyms SceneList SceneCode ScenePa SceneImg ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require AF0m SceneBCert AD2l.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require StackMalloc8Closed StackFree8Closed StackFree8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require RT_set_shadow.
Import ListNotations.
Open Scope Z_scope.
(* The rows' notations, as A/G_Close.v writes them. *)
#[local] Abbreviation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Abbreviation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation B := AD2l.TfibB (only parsing).
#[local] Notation HB := AD2l.TfibB_syms (only parsing).

(* The row stack_malloc_8_sz. *)
Lemma p_stack_malloc_8_sz : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  astack_malloc_sz_realizes SEGS B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8.
Proof.
  intros rc fx.
  refine (@StackMalloc8Closed.stack_malloc_8_sz_discharged fx rc B (SceneBCert.scene_LAWS B _) HB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - rewrite (SceneBCert.scene_tp B HB). vm_compute. reflexivity.
  - rewrite (SceneBCert.scene_tsd B HB). vm_compute. reflexivity.
  - exact (SceneBCert.scene_c_fake_stack B HB).
  - exact (SceneBCert.scene_c_tsd_slot B HB).
  - exact (SceneBCert.scene_c_dtv B HB).
  - exact (SceneBCert.scene_c_dtls B HB).
  - exact (SceneBCert.scene_c_dtls_dtv1 B HB).
  - exact (SceneBCert.scene_c_tsd_main B HB).
  - exact (SceneBCert.scene_c_ctx_thread B HB).
  - exact (SceneBCert.scene_c_thread_tls_beg B HB).
  - exact (SceneBCert.scene_c_thread_tls_end B HB).
  - exact (SceneBCert.scene_c_tls_got_mod B HB).
  - exact (SceneBCert.scene_c_tls_got_off B HB).
  - exact (SceneBCert.scene_c_real_tga B HB).
  - exact (SceneBCert.scene_c_dtv1 B HB).
  - exact (SceneBCert.scene_asan_inited_cell B HB).
  - exact (SceneBCert.scene_c_tsd_key_inited B HB).
  - exact (SceneBCert.scene_c_tsd_key B HB).
  - exact (SceneBCert.scene_c_got_cflags B HB).
  - exact (SceneBCert.scene_c_cflag_tga B HB).
  - exact (SceneBCert.scene_c_got_verb B HB).
  - exact (SceneBCert.scene_c_verb B HB).
  - exact (SceneBCert.scene_c_got_dtls B HB).
Qed.

(* The row ASF8. *)
Lemma p_ASF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8.
Proof.
  intros rc fx.
  exact (@StackFree8Closed.stack_free_8_discharged fx rc B (SceneBCert.scene_LAWS B _) HB).
Qed.

(* The row ASH00. *)
Lemma p_ASH00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Proof.
  intros rc fx.
  exact (@RT_set_shadow.scene_set_shadow_00 fx rc B (SceneBCert.scene_LAWS B _) HB).
Qed.

(* The row ASHF8. *)
Lemma p_ASHF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Proof.
  intros rc fx.
  exact (@RT_set_shadow.scene_set_shadow_f8 fx rc B (SceneBCert.scene_LAWS B _) HB).
Qed.
