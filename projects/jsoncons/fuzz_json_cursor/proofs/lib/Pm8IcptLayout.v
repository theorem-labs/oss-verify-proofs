(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8ArtFsInv.
Import ListNotations.
Open Scope Z_scope.

Record as0_icpt_layout (IL : icpt_layout) : Prop := AICL {
  aicl_strlen : icl_strlen IL = 0x6a54c;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x103c0; aicl_ro_hi : icl_ro_hi IL = 0x103e0;
  aicl_globals : icl_globals IL = ART_GLOBALS;
  aicl_poison : icl_poison IL = ART_POISON;
  aicl_memcpy : icl_memcpy IL = 0x7ee70;
  aicl_memmove : icl_memmove IL = 0x7ee6c;
  aicl_ctxslot : icl_ctxslot IL = 0x6b1f08;
  aicl_strerror_r : icl_strerror_r IL = 0x6a5c4;
  aicl_scr_strerror : icl_scr_strerror IL = 4320;
  aicl_strerror_cells : icl_strerror_cells IL = [(0x690a20, 8, 0x6b0d18); (0x6b0d40, 8, 0)];
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0x154000
}.

Record pm_icpt_layout_x (ILX : icpt_layout_x) : Prop := AICLX {
  aiclx_memcmp : iclx_memcmp ILX = 0x6a564;
  aiclx_scr_memcmp : iclx_scr_memcmp ILX = 8192;
  aiclx_cxa_atexit : iclx_cxa_atexit ILX = 0x6a62c;
  aiclx_scr_cxa : iclx_scr_cxa ILX = 512;
  aiclx_atexit_tab : iclx_atexit_tab ILX = 0x6b0aa0;
  aiclx_atcxa : iclx_atcxa ILX = 0x74c7c;
  aiclx_scr_handler : iclx_scr_handler ILX = 512;
  aiclx_annotate : iclx_annotate ILX = 0x82c5c;
  aiclx_need_locks : iclx_need_locks ILX = 0x6b0ce3;
  aiclx_memcmp2 : iclx_memcmp2 ILX = 0x6a560;
  aiclx_memset : iclx_memset ILX = 0x7ee68;
  aiclx_setsh00 : iclx_setsh00 ILX = 0x829e4;
  aiclx_setshf5 : iclx_setshf5 ILX = 0x82aec;
  aiclx_setshf8 : iclx_setshf8 ILX = 0x82b04;
  aiclx_scr_setsh : iclx_scr_setsh ILX = 256
}.

Definition pm_icptx_open (L : asan_layout) (ar : asan_run) (ILX : icpt_layout_x) (scfg : SpuriousCfg) (HI : asan_iface) : Prop :=
  amemcmp_spec L ar ILX scfg HI
  /\ amemcmp_spec_at L ar scfg HI (iclx_memcmp2 ILX) (iclx_scr_memcmp ILX)
  /\ amemset_libc_spec L ar ILX scfg HI
  /\ aset_shadow_spec L ar scfg HI (iclx_setsh00 ILX) 0 (iclx_scr_setsh ILX)
  /\ aset_shadow_spec L ar scfg HI (iclx_setshf5 ILX) 245 (iclx_scr_setsh ILX)
  /\ aset_shadow_spec L ar scfg HI (iclx_setshf8 ILX) 248 (iclx_scr_setsh ILX).
