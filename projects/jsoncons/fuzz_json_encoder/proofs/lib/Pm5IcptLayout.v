(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm5ArtFsInv.
Import ListNotations.
Open Scope Z_scope.

Record as0_icpt_layout (IL : icpt_layout) : Prop := AICL {
  aicl_strlen : icl_strlen IL = 0x6c1e8;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x103d0; aicl_ro_hi : icl_ro_hi IL = 0x103f0;
  aicl_globals : icl_globals IL = ART_GLOBALS;
  aicl_poison : icl_poison IL = ART_POISON;
  aicl_memcpy : icl_memcpy IL = 0x80b0c;        (* [comment removed for export] *)
  aicl_memmove : icl_memmove IL = 0x80b08;      (* [comment removed for export] *)
  aicl_ctxslot : icl_ctxslot IL = 0x6c2d48;     (* [comment removed for export] *)
  aicl_strerror_r : icl_strerror_r IL = 0x6c260;                                                         (* [comment removed for export] *)
  aicl_scr_strerror : icl_scr_strerror IL = 4320;                                                        (* [comment removed for export] *)
  aicl_strerror_cells : icl_strerror_cells IL = [(0x6a1860, 8, 0x6c1b58); (0x6c1b80, 8, 0)];             (* [comment removed for export] *)
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0x166000                            (* [comment removed for export] *)
}.

Record pm_icpt_layout_x (ILX : icpt_layout_x) : Prop := AICLX {
  aiclx_memcmp : iclx_memcmp ILX = 0x6c200;
  aiclx_scr_memcmp : iclx_scr_memcmp ILX = 8192;
  aiclx_cxa_atexit : iclx_cxa_atexit ILX = 0x6c2c8;
  aiclx_scr_cxa : iclx_scr_cxa ILX = 512;
  aiclx_atexit_tab : iclx_atexit_tab ILX = 0x6c18e0;
  aiclx_atcxa : iclx_atcxa ILX = 0x76918;
  aiclx_scr_handler : iclx_scr_handler ILX = 512;
  aiclx_annotate : iclx_annotate ILX = 0x848f8;
  aiclx_need_locks : iclx_need_locks ILX = 0x6c1b23;
  aiclx_memcmp2 : iclx_memcmp2 ILX = 0x6c1fc;                (* [comment removed for export] *)
  aiclx_memset : iclx_memset ILX = 0x80b04;
  aiclx_setsh00 : iclx_setsh00 ILX = 0x84680;
  aiclx_setshf5 : iclx_setshf5 ILX = 0x84788;
  aiclx_setshf8 : iclx_setshf8 ILX = 0x847a0;
  aiclx_scr_setsh : iclx_scr_setsh ILX = 256
}.

(* [comment removed for export] *)
Definition pm_icptx_open (L : asan_layout) (ar : asan_run) (ILX : icpt_layout_x) (scfg : SpuriousCfg) (HI : asan_iface) : Prop :=
  amemcmp_spec L ar ILX scfg HI
  /\ amemcmp_spec_at L ar scfg HI (iclx_memcmp2 ILX) (iclx_scr_memcmp ILX)
  /\ amemset_libc_spec L ar ILX scfg HI
  /\ aset_shadow_spec L ar scfg HI (iclx_setsh00 ILX) 0 (iclx_scr_setsh ILX)
  /\ aset_shadow_spec L ar scfg HI (iclx_setshf5 ILX) 245 (iclx_scr_setsh ILX)
  /\ aset_shadow_spec L ar scfg HI (iclx_setshf8 ILX) 248 (iclx_scr_setsh ILX).
