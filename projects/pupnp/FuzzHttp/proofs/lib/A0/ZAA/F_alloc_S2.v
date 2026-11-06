(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem AFrame ATacA ACells LJ LJU PEnv ATacFix ASec AQuar F_poison F_sec_A F_alloc_env F_alloc_A F_alloc_B F_alloc_C.
Import ListNotations.
Open Scope Z_scope.

Section RZS.
  Context {HC : HasCeiling}.
  Variable E : penv.
  Variables (gp s7 s8 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP lo B M rz size needed bs SPACE : Z) (m : mem).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis LOQ : lo <= SP - 64.
  Hypothesis SPR : SP <= 2^47.
  Hypothesis BR : 6328320 <= B /\ B mod 4096 = 0 /\ B + bs <= 2^47 /\ (B + bs <= 0x7fff8000 \/ 0x10007fff8000 <= B).
  Hypothesis BSP : 0 <= SPACE /\ SPACE + K_SPACE < 2^64 /\ (B < SPACE \/ SPACE + K_SPACE <= B).
  Hypothesis RZ : 16 <= rz <= 2048 /\ rz mod 16 = 0.
  Hypothesis HM : M = B + rz - 16.
  Hypothesis SZ : 1 <= size <= 2^28 /\ rz + rup8 size + 8 <= bs /\ 0 < needed <= 2^40 /\ bs = rup4k needed.

  Notation U := (M + 16).
  Notation TL := (bs - rz - rup8 size).

  Definition rzs_post : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x22 x25 t3 t4 t5 t6 m5 m',
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 x8 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz B) (wz needed) (wz U) (wz M) x22 s7 s8 x25 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x33af0) fc None m' (seg_rom asegs)
      /\ mstep [(SP - 64, SP); (sh B, sh B + rz / 8)] m m5
      /\ mstep [(SP - 64, SP); (sh (U + rup8 size), sh (U + rup8 size) + TL / 8)] m5 m'
      /\ stk asegs m' lo SP /\ poison_env E m'
      /\ rw_cells asegs m' (sh B) [CB (Z.to_nat (rz / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (rz / 8)))]
      /\ rw_cells asegs m' (sh (U + rup8 size)) [CB (Z.to_nat (TL / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (TL / 8)))].

  #[using="LOH LOQ SPR BR RZ HM SZ"] Lemma rzs_core : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 : list byte),
    mem_inv asegs m -> stk asegs m lo SP -> poison_env E m ->
    rw_cells asegs m SEC [C8 (wz 4096)] ->
    rw_cells asegs m (B - 4096 + 16) [C8 (wz needed)] ->
    rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) j1] ->
    rw_cells asegs m (sh (U + rup8 size)) [CB (Z.to_nat (TL / 8)) j2] ->
    evt asegs rzs_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 (wz 0) (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) (wz needed) (wz U) (wz M) (wz INSTANCE) s7 s8 (wz (U + size)) s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33a70) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j2 MI ST PE PGS HSZ SH1 SH2.
    destruct BR as (BLO & B4K & BHI & BMEM). destruct SZ as (SZ1 & SZ2 & SZ3 & EBS).
    assert (R8 : exists k, rup8 size = 8 * k /\ size <= 8 * k < size + 8) by (exists ((size + 7) / 8); unfold rup8; clear; Z.div_mod_to_equations; lia).
    destruct R8 as (k8 & ER8 & K8R).
    assert (RBS : needed <= bs < needed + 4096 /\ bs mod 4096 = 0) by (rewrite EBS; unfold rup4k; clear - SZ3; Z.div_mod_to_equations; lia).
    hideB SH1. hideB SH2.
    zstep. zstep. zstep.
    replace (Z.land 4095 B) with 0 by (change 4095 with (2^12 - 1); rewrite zb_land_mask_l by lia; change (2^12) with 4096; symmetry; exact B4K).
    zstep. if_false.
    zstep. zstep. if_false.
    zstep.
    zstep.
    zstep. zstep. zstep.
    rewrite (SysMm.land_m4096 (needed + 4095)) by (clear - SZ3; lia).
    replace (needed + 4095 - (needed + 4095) mod 4096) with bs by (rewrite EBS; unfold rup4k; clear - SZ3; Z.div_mod_to_equations; lia).
    zstep. zstep. zstep.
    assert (U8 : exists u, U = 8 * u) by (exists ((M + 16) / 8); subst M; clear - B4K RZ; Z.div_mod_to_equations; lia).
    destruct U8 as (u8 & EU8).
    rewrite (land_m8 (U + size + 7)) by (subst M; clear - BLO BHI RZ SZ1 SZ2 K8R ER8; lia).
    replace (U + size + 7 - (U + size + 7) mod 8) with (U + rup8 size) by (rewrite ER8, EU8; clear - K8R; Z.div_mod_to_equations; lia).
    zstep. zstep. zstep.
    replace (U - B) with rz by (subst M; clear; lia).
    clear HSZ. zstep.
    assert (QBp : 0x10007fff8000 <= lo /\ lo <= SP - 64 /\ SP <= 2^47) by (split; [exact LOH| split; [exact LOQ| exact SPR]]).
    assert (SHD : sh (U + rup8 size) = sh B + rz / 8 + k8 /\ 2147450880 <= sh B /\ sh B + bs / 8 <= 17594333495296 /\ rz / 8 * 8 = rz /\ 0 <= TL /\ TL / 8 * 8 = TL
                  /\ rz / 8 + k8 + TL / 8 = bs / 8).
    { rewrite ER8. subst M. unfold sh, SHADOW_OFF. clear - BLO B4K BHI RZ SZ2 ER8 K8R RBS. Z.div_mod_to_equations. lia. }
    destruct SHD as (SHD1 & SHD2 & SHD3 & SHD4 & SHD5 & SHD6 & SHD7).
    callk (poison_shadow_spec_all E _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP lo B rz 250 m MI QBp);
      [ split; [clear - B4K; Z.div_mod_to_equations; lia|]; split; [clear - RZ; Z.div_mod_to_equations; lia|]; split; [clear - RZ; lia|]; split; [| clear; lia];
        unfold poison_range; clear - BLO BHI BMEM RZ SZ1 SZ2 K8R ER8; lia
      | exact PE | exact ST | exact SH1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    rename MUk into MU5, WMk into WM5, MI0 into MI5, PC into ST5, PC0 into PE5, POST into SHL.
    unhideB SH2.
    eapply (rw_cells_transport asegs _ m m5) in SH2; [| exact MU5| exact WM5| cbn [disjoint_from]; simpl_sizes; rewrite SHD1; clear - SHD2 SHD3 SHD4 SHD5 SHD6 SHD7 LOH LOQ K8R SZ1; repeat split; lia].
    hideB MU5. hideB WM5. hideB SHL. pose proof MI5 as MI5c. hideB MI5c.
    zstep. zstep.
    replace (B - (U + rup8 size) + bs) with TL by (subst M; clear; lia).
    zstep. zstep. zstep.
    callk (poison_shadow_spec_all E _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP lo (U + rup8 size) TL 250 m5 MI5 QBp);
      [ split; [rewrite ER8, EU8; clear; Z.div_mod_to_equations; lia|]; split; [clear - SHD6; Z.div_mod_to_equations; lia|]; split; [exact SHD5|]; split; [| clear; lia];
        unfold poison_range; subst M; clear - BLO BHI BMEM RZ SZ1 SZ2 K8R ER8; lia
      | exact PE5 | exact ST5 | exact SH2 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    unhideB SHL.
    eapply (rw_cells_transport asegs _ m5 m6) in SHL; [| exact MUk| exact WMk| cbn [disjoint_from]; simpl_sizes; rewrite SHD1; clear - SHD2 SHD3 SHD4 SHD5 SHD6 SHD7 LOH LOQ K8R SZ1 RZ; repeat split; lia].
    unhideB MU5. unhideB WM5. unhideB MI5c.
    apply evt_done. unfold rzs_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m5, m6.
    split; [reflexivity|]. split; [exact (conj MU5 (conj WM5 MI5c))|]. split; [exact (conj MUk (conj WMk MI0))|].
    split; [exact PC|]. split; [exact PC0|]. split; [exact SHL| exact POST].
  Qed.

  #[using="LOH LOQ SPR BR BSP RZ HM SZ"] Lemma rzs_spec : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 j2 : list byte),
    mem_inv asegs m -> stk asegs m lo SP -> poison_env E m ->
    rw_cells asegs m 721592 [C8 (wz SPACE)] -> rw_cells asegs m SEC [C8 (wz 4096)] ->
    rw_cells asegs m (B - 4096 + 16) [C8 (wz needed)] ->
    rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) j1] ->
    rw_cells asegs m (sh (U + rup8 size)) [CB (Z.to_nat (TL / 8)) j2] ->
    evt asegs rzs_post
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 (wz 0) (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) (wz needed) (wz U) (wz M) (wz INSTANCE) s7 s8 (wz (U + size)) s10 s11 t3 t4 t5 t6)
          F_ (wz 0x33a14) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j2 MI ST PE SPC PGS HSZ SH1 SH2.
    pose proof BR as (BLO & B4K & BHI & BMEM). pose proof BSP as (SP0 & SPH & BAP).
    assert (BRG : 0 <= B < 2^64) by (destruct SZ as (SZ1 & SZ2 & _); destruct RZ as (RZ1 & _); unfold rup8 in SZ2; clear - BLO BHI SZ1 SZ2 RZ1; Z.div_mod_to_equations; lia).
    hideB SH1. hideB SH2. hideB HSZ.
    zstep. if_true.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    - unhideB SH1. unhideB SH2. unhideB HSZ. eapply rzs_core; eassumption.
    - zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC.
      + unhideB SH1. unhideB SH2. unhideB HSZ. eapply rzs_core; eassumption.
      + exfalso. clear - KB KC BAP. lia.
  Qed.
End RZS.

