(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillSeamcf.v (commit 3cae605a900a, blob 6af4d2115859) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import YFk5cf YFk8cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRmodel YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Definition refill_B3_case_cf (Q : Z -> Z -> Prop) : Prop :=
forall (Hp : list Z) (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z)
  (mat0 : list word) (msJ : machine_state) (B : asyms) (S : astate),
let sp0 := bv_unsigned (getr regs0 2) in
let T := ly_T ly in
img_cover ly -> layout_ok ly -> 1 <= c <= 31 -> maxc = max_cached c -> n = maxc / 2 -> csz = class_size c ->
(0 <= nf /\ 4 * nf <= mf) -> (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) ->
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) ->
0 <= j64 < 2 ^ 32 -> 0 <= jna < 2 ^ 64 -> 0 <= jnf < 2 ^ 64 -> 0 <= jsm < 2 ^ 64 -> 0 <= jm1 < 2 ^ 64 -> 0 <= jm2 < 2 ^ 64 -> 0 <= jex < 2 ^ 8 ->
(ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) -> ly_stk_lo ly + REP_W c <= sp0 ->
YK0s.ret_ok (getr regs0 1) -> 4096 <= bv_unsigned (getr regs0 1) -> getr regs0 4 = w64 TFIB_TP ->
getr regs0 10 = w64 (T + t_cache) -> getr regs0 11 = w64 (@YFk5cf.Pr ly c) -> getr regs0 12 = w64 A_ALLOCATOR ->
getr regs0 13 = w64 c ->
nf < n -> mu - au < kUserMapSize + kMaxSize -> au mod csz = 0 -> need = n - nf -> tot = au + need * csz ->
adr = @YFk5cf.RBv ly c + mu -> sha = YFk5cf.SHBv + adr / 8 -> mu2 = mu + kUserMapSize -> nce = (mu - au) / csz ->
ncg = (mu2 - au) / csz -> nfe = nf + nce -> nfg = nf + ncg -> fadr = @YFk5cf.FAv ly c + mf -> shf = YFk5cf.SHBv + fadr / 8 ->
mf2 = mf + kFreeArrayMapSize -> aue = au + nce * csz -> aug = au + ncg * csz ->
@YFk5cf.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg
  fadr shf mf2 aue aug W md0 (@YFk5cf.WINR0 ly regs0 c) (fun _ => True) YFk8cf.R3_J W
  (mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0)) ->
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
(forall a, sp0 - REP_W c <= a < sp0 -> apresent (w_H W) mem0 a) ->
(forall a, @YFk5cf.DSTv ly c <= a < @YFk5cf.DSTv ly c + 64 -> apresent (w_H W) mem0 a) ->
(forall a, @YFk5cf.FAv ly c <= a < @YFk5cf.FAv ly c + mf -> apresent (w_H W) mem0 a) ->
TfibSyms B -> ly_tsd ly = TFIB_TSD ->
ARmcf B ly S Hp (aview tfibsegs (w_H W) mem0) ->
getr regs0 3 = w64 (as_gp B) -> st_cache_inited S = true -> pc_chunks (cache S c) = [] ->
nf = fa_len (rg_free (reg S c)) -> mf = rg_mapped_fa (reg S c) -> au = rg_alloc_user (reg S c) ->
mu = rg_mapped_user (reg S c) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 64) 4 j64 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 72) 8 jna ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 80) 8 jnf ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 68) 1 jex ->
exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
qloose S -> ARcf tfibsegs B ly S Hp W mem0 md0 -> xs_mapped_cf ly S md0 ->
(c = kBatchClass -> batch_room_cf S) -> (c <> kBatchClass -> ERRB_ROOM S /\ WfP_cf (as_universe B) 1 1 0 S) ->
WfP_cf (as_universe B) 1 0 0 S ->
arodata_ok_cf tfibsegs B mem0 -> cf_hull_ok S ->
Q mu tot ->
amreal tfibsegs (refill_tree_cf c S) W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0))
  (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0).

Definition refill_B3_inner_cf : Prop := refill_B3_case_cf (fun _ _ => True).

Definition refill_B3_classfull_cf : Prop :=
  refill_B3_case_cf (fun mu tot => mu < tot /\ kFreeArrayOffset < mu + kUserMapSize).

Section b.
Context {IM : AImg} {AG : AGImg}.
Variable B : asyms.
Variable IOK : Z -> Prop.

Definition refill_case_cf (P : astate -> Z -> Prop) : Prop :=
forall Hp inst ly S W regs mem md c,
refill_state_gen_cf B IOK Hp inst ly S W mem md c ->
arodata_ok_cf im_segs B mem -> cf_hull_ok S ->
refill_call_gen_cf B inst ly W regs mem c ->
P S c ->
amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs mem md) (refill_leaf_core_cf B Hp ly S c W regs mem md).

Definition refill_B3_entry_cf : Prop :=
refill_case_cf (fun S c => st_cache_inited S = true /\ fa_len (rg_free (reg S c)) < max_cached c / 2).

Definition refill_B2_entry_cf : Prop :=
refill_case_cf (fun S c => st_cache_inited S = true /\ max_cached c / 2 <= fa_len (rg_free (reg S c))).

Definition refill_uninit_entry_cf : Prop :=
refill_case_cf (fun S _ => st_cache_inited S = false).

Lemma refill_spec_core_cf_of_cases :
  refill_B3_entry_cf -> refill_B2_entry_cf -> refill_uninit_entry_cf -> refill_spec_core_cf B IOK.
Proof.
intros H3 H2 HU Hp inst ly S W regs mem md c HS HRO HH HC.
destruct (st_cache_inited S) eqn:EI.
- destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [L|L].
  + exact (H3 Hp inst ly S W regs mem md c HS HRO HH HC (conj EI L)).
  + exact (H2 Hp inst ly S W regs mem md c HS HRO HH HC (conj EI L)).
- exact (HU Hp inst ly S W regs mem md c HS HRO HH HC EI).
Qed.
End b.
End a.
