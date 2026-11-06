(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section IIfaceDrv.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IL : icpt_layout.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Record aicpt_ok : Prop := AICOK {
  aic_strlen : astrlen_spec L ar IL scfg HI;
  aic_globals : rt_globals IL HI;
  aic_img_shadow : rt_img_shadow L IL HI;
  aic_shadow_defined : rt_shadow_defined HI;
  aic_tls : rt_tls L ar IL HI;
  aic_memcpy_libc : amemcpy_libc_spec L ar IL scfg HI;
  aic_memmove_libc : amemmove_libc_spec L ar IL scfg HI
}.

Lemma aicpt_of_pm : forall (ILX : icpt_layout_x) (ANN : Prop), pm_aicpt_ok L ar IL ILX scfg HI ANN -> aicpt_ok.
Proof.
  intros ILX ANN H. constructor;
    [exact (pic_strlen _ _ _ _ _ _ _ H) | exact (pic_globals _ _ _ _ _ _ _ H) | exact (pic_img_shadow _ _ _ _ _ _ _ H) | exact (pic_shadow_defined _ _ _ _ _ _ _ H)
    | exact (pic_tls _ _ _ _ _ _ _ H) | exact (pic_memcpy_libc _ _ _ _ _ _ _ H) | exact (pic_memmove_libc _ _ _ _ _ _ _ H)].
Qed.
End IIfaceDrv.
