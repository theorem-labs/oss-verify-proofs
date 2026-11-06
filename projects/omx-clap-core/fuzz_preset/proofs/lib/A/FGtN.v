(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/FGtN.v (commit 67deba317dfb, blob 6abcfed908f2) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB19 AF0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFl1 AFhy AFis AFkp AFk6 AFk5 AFhz AFk8 AFk9.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import FGsN.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFkn FGwN FGkN FGcN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section f.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c cnt : Z).

Variables (j80 j88 jst : Z).

Variables (nf au mu : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let mf : Z := rg_mapped_fa (reg S c).
Let fadr : Z := AFk5.FAv ly c + mf.
Let shf : Z := AFk5.SHBv + fadr / 8.
Let mf2 : Z := mf + kFreeArrayMapSize.

Definition efa_pre_lk : Prop :=
  img_cover ly /\ layout_ok ly /\ TfibSyms B /\ ly_tsd ly = TFIB_TSD /\
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) /\
  1 <= c <= 31 /\ 0 <= cnt <= 2 ^ 27 /\
  (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
  4 * cnt <= mf + kFreeArrayMapSize /\
  YK0s.ret_ok (getr regs0 1) /\ getr regs0 4 = w64 TFIB_TP /\
  getr regs0 10 = w64 A_ALLOCATOR /\ getr regs0 11 = w64 (AFk5.RGv ly c) /\
  getr regs0 12 = w64 (AFk5.RBv ly c) /\ getr regs0 13 = w64 cnt /\
  (ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) /\
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) /\
  (forall a, (AFk5.RGv ly c <= a < AFk5.RGv ly c + 128) \/ (AFk5.Pr ly c <= a < AFk5.Pr ly c + 16) \/
             (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) mem0 a) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 24) 8 mf /\
  (exists jm1 jm2, 0 <= jm1 < 2 ^ 64 /\ 0 <= jm2 < 2 ^ 64 /\
     val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1 /\
     val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2) /\

  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c) 8 LOCKV /\
  (0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 80) 8 j80) /\
  (0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 88) 8 j88) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.Pr ly c + 0) 4 (max_cached c / 2) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.Pr ly c + 8) 8 (class_size c) /\
  (0 <= jst < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 jst) /\

  (0 <= nf /\ 4 * nf <= mf) /\ (0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 8) 8 0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 16) 8 nf /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 32) 8 au /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 40) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 48) 8 mu /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 56) 8 0 /\

  (exists j68, 0 <= j68 < 2 ^ 8 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 68) 1 j68) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.Pr ly c + 4) 4 (max_cached c) /\
  (mf < 4 * cnt ->
     mf + kFreeArrayMapSize <= kFreeArrayMax /\
     region_free (vm_reserved (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     map_contains (vm_maps (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     amwf md0 /\ YM05.ceil_of_top (alloc_top (m_vmmaps md0)) /\
     eager_used md0 + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md0) /\
     (forall a, AFkn.SHR shf a -> mem0 (w64 a) <> None)).

Definition efa_leafT_lk (r : bool * astate) (W' : world tfibsegs) (c' : config) : Prop :=

  exists j68, val_mem tfibsegs (mrestrict (w_H W) mem0) (AFk5.RGv ly c + 68) 1 j68 /\
  @FGcN.efa_leaf _ W ly regs0 mem0 md0 c (max_cached c) (max_cached c / 2) nf mf au mu (class_size c) j68 j80 j88 jst cnt fadr shf mf2 S r W' c'.

Theorem tfib_efa_spec_lk : forall (k : bool -> M unit) (Q : unit * astate -> world tfibsegs -> config -> Prop),
  efa_pre_lk ->
  (forall r W' c', efa_leafT_lk r W' c' -> amreal tfibsegs (k (fst r) (snd r)) W' c' Q) ->
  amreal tfibsegs (bind (ensure_free_array c cnt true) k S) W (cfg_at tfibsegs A_EFA regs0 mem0 md0) Q.
Proof.
  intros k Q PRE Hk.
  destruct PRE as (IMG & LY & TS & HTSD & Hconst & HcR & Hcnt & Hmf & Hone & Hra & Htp & Ha0 & Ha1 & Ha2 & Ha3 &
                   Hsp & Hpres0R & Hcells & Hmfv & (jm1 & jm2 & Hjm1 & Hjm2 & Hjm1v & Hjm2v) & Hlk & [H80r Hk80] & [H88r Hk88] & Hkp & Hks & [Hstr Hkt] & Hnf0 & Hmu0 & Hk8 & Hk16 & Hk32 & Hk40 & Hk48 & Hk56 & (j68 & Hj68 & Hk68v) & Hkmax & Hgrow).
  assert (Hz32 : 0 <= 0 < 2 ^ 32) by lia.
  assert (Hz64 : 0 <= 0 < 2 ^ 64) by lia.
  assert (Hz32' : 0 <= j68 < 2 ^ 32) by lia.
  exact (@FGcN.efa_call _ _ W ly regs0 mem0 md0 c (max_cached c) (max_cached c / 2) nf mf au mu (class_size c)
    j68 j80 j88 jst jm1 jm2 1 16 fadr shf kUserMapSize 0 0 cnt 0 fadr shf mf2 0 0
    IMG LY HcR eq_refl eq_refl eq_refl Hnf0 Hmf Hmu0
    Hz32' H80r H88r Hstr Hjm1 Hjm2 Hsp Hra Htp Ha0 Ha1 Ha2 Ha3
    eq_refl eq_refl eq_refl Hcnt eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    B TS HTSD Hconst Hpres0R Hcells Hmfv Hjm1v Hjm2v Hlk Hk80 Hk88 Hkp Hks Hkt Hk8 Hk16 Hk32 Hk40 Hk48 Hk56 (conj Hj68 Hk68v) Hkmax S k Q eq_refl Hone Hgrow
    (fun r W' c' L => Hk r W' c' (ex_intro _ j68 (conj Hk68v L)))).
Qed.
End f.
End d.
