(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdR.v (commit 67deba317dfb, blob 89aa77a374b3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgk AFez AFk5 AFkn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FGcN.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgA ADIfaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
#[local] Existing Instance AImgA.AImg_A.
#[local] Existing Instance ADIfaceA.DImg_A.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section r.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.

Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

Local Notation m_of W mem := (mrestrict (w_H W) mem).

Definition rd_geo : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
layout_ok ly /\ img_cover ly /\ ly_tsd ly = TFIB_TSD.

Definition rd_thread : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> apresent (w_H W) mem a.
Definition rd_rinfo : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
forall a, AFgk.RGv ly c <= a < AFgk.RGv ly c + 128 -> apresent (w_H W) mem a.
Definition rd_fa : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
forall a, AFgk.FAv ly c <= a < AFgk.FAv ly c + rg_mapped_fa (reg X c) -> apresent (w_H W) mem a.

Definition rd_cache : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 -> st_cache_inited X = true ->
val_mem tfibsegs (m_of W mem) (AFgk.PCv ly c) 4 (Z.of_nat (length (pc_chunks (cache X c)))) /\
val_mem tfibsegs (m_of W mem) (AFgk.PCv ly c + 4) 4 (AFgk.MAXv c) /\
val_mem tfibsegs (m_of W mem) (AFgk.PCv ly c + 8) 8 (AFgk.SZv c) /\
(forall (i : nat) v, nth_error (pc_chunks (cache X c)) i = Some v ->
 val_mem tfibsegs (m_of W mem) (AFgk.PCv ly c + 16 + 4 * Z.of_nat i) 4 (v / 16)).
Definition rd_region : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
let RG := AFgk.RGv ly c in
val_mem tfibsegs (m_of W mem) RG 8 0 /\ val_mem tfibsegs (m_of W mem) (RG + 8) 8 0 /\
val_mem tfibsegs (m_of W mem) (RG + 16) 8 (fa_len (rg_free (reg X c))) /\
val_mem tfibsegs (m_of W mem) (RG + 24) 8 (rg_mapped_fa (reg X c)) /\
val_mem tfibsegs (m_of W mem) (RG + 32) 8 (rg_alloc_user (reg X c)) /\ val_mem tfibsegs (m_of W mem) (RG + 40) 8 0 /\
val_mem tfibsegs (m_of W mem) (RG + 48) 8 (rg_mapped_user (reg X c)) /\
val_mem tfibsegs (m_of W mem) (RG + 56) 8 0.

Definition rd_img : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly).

Definition rd_inst : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md -> inst = as_inst B.

Definition rd_budget_x : Prop :=
forall inst ly X z W regs mem md, cd_pre_x B ARXr inst ly X z W regs mem md ->

forall its zs, DRq X its zs ->
rg_mapped_fa (reg X kBatchClass) < 4 * (fa_len (rg_free (reg X kBatchClass)) + max_cached kBatchClass / 2) ->
eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).

Definition rd_own : Prop :=
forall inst ly X W mem md c off, ARXr inst ly X W mem md -> cd_model RMAXD X c off ->
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
forall a, AFgk.WINF ly c cnt a \/ AFgk.WINR ly c cnt (fa_len (rg_free (reg X c))) a -> AOX ly X a.

Definition rd_len : Prop :=
forall inst ly X W mem md, ARXr inst ly X W mem md ->
(32 <= length (st_cache X))%nat /\ (32 <= length (st_regions X))%nat.

Definition rd_user : Prop :=
forall inst ly X W mem md c', ARXr inst ly X W mem md -> 1 <= c' <= 31 ->
0 <= rg_alloc_user (reg X c') <= rg_mapped_user (reg X c') /\ rg_mapped_user (reg X c') <= kFreeArrayOffset /\
rg_mapped_user (reg X c') mod kUserMapSize = 0 /\ rg_alloc_user (reg X c') mod 16 = 0.

Definition rd_grow : Prop :=
forall inst ly X W mem md c, ARXr inst ly X W mem md -> 1 <= c <= 30 ->
let mf := rg_mapped_fa (reg X c) in
let fadr := AFk5.FAv ly c + mf in
mf + kFreeArrayMapSize <= kFreeArrayMax ->

eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md) ->
region_free (vm_reserved (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
amwf md /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
(forall a, AFkn.SHR (AFk5.SHBv + fadr / 8) a -> mem (w64 a) <> None).

Definition rd_growT : Prop :=
forall inst ly X W regs mem md c off W3 mem1 mem' matN mat',
ARXr inst ly X W mem md -> cd_model RMAXD X c off ->
let sp0 := bv_unsigned (getr regs 2) in
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
let old := fa_len (rg_free (reg X c)) in
let mf := rg_mapped_fa (reg X c) in
let N := AFgk.Nv c in
let RG := AFgk.RGv ly c in
let fadr := AFk5.FAv ly c + mf in
let shf := AFk5.SHBv + fadr / 8 in
let md2 := grant_md false AFkn.FL50 (w64 fadr) (w64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md) in
let S'' := YFfh.XK_push c off (YFfh.XK_drain c (YG06.upd_reg c (FGcN.rgG (reg X c)) X)) in
let WING1 := fun a =>
  (sp0 - 240 - RSTACK <= a < sp0) \/ (RG + 24 <= a < RG + 32) \/ (RG + 64 <= a < RG + 68) \/ (RG + 69 <= a < RG + 128) \/
  (ly_T ly + 2768 <= a < ly_T ly + 2800) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) \/ AFkn.RANGE fadr a \/ AFkn.SHR shf a in
let WINT := fun a =>
  (sp0 - 320 <= a < sp0) \/ (AFgk.PCv ly c <= a < AFgk.PCv ly c + 4) \/ (AFgk.SLOTv ly c cnt <= a < AFgk.SLOTv ly c cnt + 4) \/
  (ly_T ly + t_cache + 2576 <= a < ly_T ly + t_cache + 2584) \/
  (RG <= a < RG + 8) \/ (RG + 16 <= a < RG + 24) \/ (RG + 80 <= a < RG + 88) \/
  (AFgk.DSTv ly c old <= a < AFgk.DSTv ly c old + 4 * N) in

ly_stk_lo ly + KSTACK_CF <= sp0 <= ly_stk_hi ly ->
cnt = AFgk.MAXv c -> mf < 4 * (old + N) ->

wle W W3 -> w_A W3 = (shf, shf + 32768) :: (fadr, fadr + kUserMapSize) :: w_A W -> hsub (w_H W3) (w_H W) ->
(forall a : word, w_H W a = false -> w_H W3 a = false) ->
(forall a : word, ~ AFkn.RANGE fadr (bv_unsigned a) -> ~ AFkn.SHR shf (bv_unsigned a) -> w_H W3 a = w_H W a) ->
A_bytes (w_A W3) = A_bytes (w_A W) + kUserMapSize + 32768 ->
AI tfibsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md md2 -> eager_used md2 <= eager_used md + kUserMapSize ->

(forall x : word, ~ WING1 (bv_unsigned x) -> mem1 x = mem x) ->
(forall a, WING1 a -> apresent (w_H W3) mem1 a) ->
(let m1 := mrestrict (w_H W3) mem1 in
 val_mem tfibsegs m1 RG 8 0 /\ val_mem tfibsegs m1 (RG + 16) 8 old /\ val_mem tfibsegs m1 (RG + 24) 8 (mf + kFreeArrayMapSize) /\
 (forall a, AFkn.RANGE fadr a -> mem1 (w64 a) = Some (Z_to_bv 8 0)) /\
 (forall a, AFkn.SHR shf a -> mem1 (w64 a) = Some (Z_to_bv 8 250))) ->

(forall x : word, ~ WINT (bv_unsigned x) -> mem' x = mem1 x) ->
(forall a, WINT a -> apresent (w_H W3) mem' a) ->
(let m := mrestrict (w_H W3) mem' in
 val_mem tfibsegs m (AFgk.PCv ly c) 4 (AFgk.CNTPv c cnt + 1) /\
 val_mem tfibsegs m (AFgk.SLOTv ly c cnt) 4 (AFgk.RELv c off / 16) /\
 val_mem tfibsegs m RG 8 0 /\ val_mem tfibsegs m (RG + 16) 8 (old + N) /\
 (forall i v, 0 <= i < N -> val_mem tfibsegs (m_of W mem) (AFgk.SRCv ly c cnt + 4 * i) 4 v ->
   val_mem tfibsegs m (AFgk.DSTv ly c old + 4 * i) 4 v)) ->
ARXr inst ly S'' W3 mem' (with_vm_backing (m_vm_lazy md2) mat' md2) /\
(forall a, AOX ly S'' a -> AOX ly X a) /\
(forall a, WING1 a -> ~ (sp0 - 240 - RSTACK <= a < sp0) -> AOX ly X a).

Definition rd_step : Prop :=
forall inst ly X W regs mem md c off mem' mat,
ARXr inst ly X W mem md -> cd_model RMAXD X c off ->

ly_stk_lo ly + KSTACK_CF <= bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
let cnt := Z.of_nat (length (pc_chunks (cache X c))) in
let old := fa_len (rg_free (reg X c)) in
let mf := rg_mapped_fa (reg X c) in
4 * (old + (if cnt =? AFgk.MAXv c then AFgk.Nv c else 0)) <= mf ->
AFgk.MEQ ly regs mem c cnt old mem' ->
(forall a, AFgk.WIN ly regs c cnt old a -> apresent (w_H W) mem' a) ->
val_mem tfibsegs (m_of W mem') (AFgk.PCv ly c) 4 (AFgk.CNTPv c cnt + 1) ->
val_mem tfibsegs (m_of W mem') (AFgk.SLOTv ly c cnt) 4 (AFgk.RELv c off / 16) ->
(cnt = AFgk.MAXv c ->
 val_mem tfibsegs (m_of W mem') (AFgk.RGv ly c) 8 0 /\
 val_mem tfibsegs (m_of W mem') (AFgk.RGv ly c + 16) 8 (old + AFgk.Nv c) /\
 val_mem tfibsegs (m_of W mem') (AFgk.RGv ly c + 24) 8 mf /\
 (forall i v, 0 <= i < AFgk.Nv c -> val_mem tfibsegs (m_of W mem) (AFgk.SRCv ly c cnt + 4 * i) 4 v ->
  val_mem tfibsegs (m_of W mem') (AFgk.DSTv ly c old + 4 * i) 4 v)) ->
ARXr inst ly (AFez.S' X c off) W mem' (with_vm_backing (m_vm_lazy md) mat md) /\
(forall a, AOX ly (AFez.S' X c off) a -> AOX ly X a).

Record cd_reads : Prop := CdReads {
  cr_geo : rd_geo; cr_thread : rd_thread; cr_rinfo : rd_rinfo; cr_fa : rd_fa;
  cr_cache : rd_cache; cr_region : rd_region; cr_img : rd_img; cr_inst : rd_inst; cr_own : rd_own;
  cr_len : rd_len; cr_user : rd_user;
  cr_grow : rd_grow; cr_budget_x : rd_budget_x; cr_growT : rd_growT; cr_step : rd_step
}.
End r.
End d.
