(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdGI.v (commit 67deba317dfb, blob 12086d36512d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMcdGk DMcdK FGsN FGtN.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z) (X : astate).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let m0 := mrestrict (w_H W) mem0.
Let PCv : Z := DMcdGk.PCv ly c.
Let RGv : Z := DMcdGk.RGv ly c.
Let SLOTv : Z := DMcdGk.SLOTv ly c cnt.
Let DSTv : Z := DMcdGk.DSTv ly c old.
Let SRCv : Z := DMcdGk.SRCv ly c cnt.
Let Nv : Z := max_cached c / 2.

Definition at_EFA (c9 : config) : Prop :=
  exists ms9 mat9 (E : env),
    c9 = mkCfg ms9 (with_vm_backing (m_vm_lazy md0) mat9 md0) /\
    (forall k, (k < aHAVf)%nat -> ew E k = ew (DMcdGk.E0 ly regs0 c off cnt old mf j80 j88 jst) k) /\
    st_ok tfibsegs E DMcdK.K9 (restrict (w_H W) ms9) /\
    DMcdGk.MEQX ly regs0 mem0 c cnt (ms_mem ms9).

Definition efa_mach (c9 : config) : Prop :=
  exists regs9 mem9 mat9,
    c9 = mkCfg (mkst regs9 (w64 FGsN.A_EFA) mem9 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat9 md0) /\
    getr regs9 1 = w64 FGsN.A_RTA_EFA /\ getr regs9 2 = Z_to_bv 64 (sp0 - 240) /\ getr regs9 4 = w64 TFIB_TP /\
    getr regs9 10 = w64 A_ALLOCATOR /\ getr regs9 11 = w64 RGv /\ getr regs9 12 = w64 (DMcdGk.RBv ly c) /\
    getr regs9 13 = w64 (old + Nv) /\
    (forall a, (sp0 - 320 <= a < sp0) \/ (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88) \/
               (PCv <= a < PCv + 4) \/ (T + 2784 <= a < T + 2792) -> apresent (w_H W) mem9 a) /\
    let m := mrestrict (w_H W) mem9 in
    val_mem tfibsegs m RGv 8 (2 ^ 60) /\ val_mem tfibsegs m (RGv + 16) 8 old /\ val_mem tfibsegs m (RGv + 24) 8 mf /\
    val_mem tfibsegs m (RGv + 80) 8 j80 /\ val_mem tfibsegs m (RGv + 88) 8 j88 /\
    val_mem tfibsegs m PCv 4 Nv /\ val_mem tfibsegs m (PCv + 8) 8 (class_size c) /\ val_mem tfibsegs m (T + 2784) 8 jst.

Definition WING (a : Z) : Prop :=
  (sp0 - 320 <= a < sp0) \/ (PCv <= a < PCv + 4) \/ (SLOTv <= a < SLOTv + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584) \/
  (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88) \/ (DSTv <= a < DSTv + 4 * Nv).

Definition at_RETKG (W3 : world tfibsegs) (md3 : Model) (mem3 : word -> option byte) (mf2 : Z)
    (W' : world tfibsegs) (cfg' : config) : Prop :=
  W' = W3 /\ exists regs' mem' mat,
    cfg' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md3) mat md3) /\
    getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r DMcdGk.SREGS -> getr regs' r = getr regs0 r) /\
    (forall x : word, ~ WING (bv_unsigned x) -> mem' x = mem3 x) /\
    (forall a, WING a -> apresent (w_H W3) mem' a) /\
    let m := mrestrict (w_H W3) mem' in
    val_mem tfibsegs m PCv 4 (DMcdGk.CNTPv c cnt + 1) /\ val_mem tfibsegs m SLOTv 4 (DMcdGk.RELv c off / 16) /\
    val_mem tfibsegs m RGv 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 (old + Nv) /\ val_mem tfibsegs m (RGv + 24) 8 mf2 /\
    (forall i v, 0 <= i < Nv -> val_mem tfibsegs m0 (SRCv + 4 * i) 4 v -> val_mem tfibsegs m (DSTv + 4 * i) 4 v).

Definition w2_t : Prop :=
  DMcdGk.free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst ->
  cnt = max_cached c -> rg_mapped_fa (reg X c) = mf -> mf < 4 * (old + Nv) ->
  (Z.to_nat c < length (st_regions X))%nat ->
  forall c9, at_EFA c9 ->
  forall regs9 mem9 md9, c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 md9 ->
  forall r W' c', FGtN.efa_leafT_lk ly X W regs9 mem9 md9 c (old + Nv) j80 j88 jst old (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c)) r W' c' ->
  SRr tfibsegs W' c' (at_RETKG W' (cfg_model c') (ms_mem (cfg_ms c')) (rg_mapped_fa (reg (snd r) c))).
End g.
End d.
