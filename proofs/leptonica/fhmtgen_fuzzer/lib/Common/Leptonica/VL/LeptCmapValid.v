(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 RCodeVL_24000_25000.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr LeptCmap LeptCmapDeser MaxIndex.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section CmapValid.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
  Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).

  #[local] Definition FR5 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  (* [comment removed for export] *)
  Lemma pv_A : forall regs m (s cm pv : Z) (cv : cmapv) (pix ret : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> CMAPat m cm cv ->
    (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z -> c_nalloc cv = (2 ^ c_d cv)%Z -> (1 <= c_n cv <= c_nalloc cv)%Z ->
    (1 <= c_arr cv)%Z -> (1 <= cm)%Z -> (cm + 24 <= s - 48)%Z -> (cm mod 8 = 0)%Z -> (pv mod 4 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = pix -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x244bc) m rom)
                  (mkst regs' (rl dVL_244bc 0x24534) (wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 (c_d cv) /\ getr regs' 18 = Z_to_bv 64 cm
      /\ getr regs' 13 = Z_to_bv 64 (c_nalloc cv) /\ getr regs' 14 = Z_to_bv 64 (c_n cv) /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 11 = pix /\ getr regs' 12 = Z_to_bv 64 pv
      /\ regs_agree (fun r => In r [2; 8; 10; 13; 14; 18]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m s cm pv cv pix ret Hs Hpv Hpv64 CM Hd Hna Hn Harr Hcm Hcmhi ALc ALp SOK SOKp H2 H1 H10 H11 H12.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF). pose proof (cf_d _ CWF). pose proof (cf_nalloc _ CWF). pose proof (cf_n _ CWF).
    assert (Hpow : (2 <= 2 ^ c_d cv <= 256)%Z) by (destruct Hd as [E|[E|[E|E]]]; rewrite E; cbn; lia).
    unfold FR5. eexists. split.
    - zv F_244bc D_244bc (Z_to_bv 64 (s - 48)).
      stepST F_244c0 D_244c0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_244c4 D_244c4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_244c8 D_244c8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_244cc D_244cc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_244d0 D_244d0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_244d4 D_244d4 ltac:(condZ).
      guard4 F_244d8 D_244d8 ALp. stepb_ft F_244dc D_244dc ltac:(condZ).
      stepST F_244e0 D_244e0 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      stepb_ft F_244e4 D_244e4 ltac:(condZ).
      guard8 F_244e8 D_244e8 ALc. stepb_ft F_244ec D_244ec ltac:(condZ).
      stepLD F_244f0 D_244f0 (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_arr SEGS _ _ _ CM)) ltac:(apply lez8; lia).
      stepb_ft F_244f4 D_244f4 ltac:(condZ).
      stepLD F_244f8 D_244f8 (Z_to_le_bytes 4 (c_d cv)) (Z_to_bv 64 (c_d cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_d SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_d cv)) by lia.
      sn F_244fc D_244fc.
      stepb_ft F_24500 D_24500 ltac:(condZ).
      sn F_24504 D_24504. sn F_24508 D_24508. sn F_2450c D_2450c.
      stepb_ft F_24510 D_24510 ltac:(pin; apply cdepth_test_ok; exact Hd).
      sn F_24514 D_24514.
      stepLD F_24518 D_24518 (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_nalloc SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      sn F_2451c D_2451c.
      sn F_24520 D_24520. rewrite (sllw_1 _ Hd), <- Hna.
      stepb_ft F_24524 D_24524 ltac:(condZ).
      stepLD F_24528 D_24528 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; repeat rdn_peel1; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_2452c D_2452c ltac:(condZ).
      stepb_ft F_24530 D_24530 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Definition pv_cells (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  (* [comment removed for export] *)
  Lemma pv_Z : forall regs m (s pv : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24534) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m s pv ret s0v s1v s2v s3v Hs Hpv Hpv64 Hret SOKp (R1 & R2 & R3 & R4 & R5) H2 H11 H12. eexists. split.
    - stepb_tk F_24534 D_24534 ltac:(condZ).
      sn F_24794 D_24794. sn F_24798 D_24798.
      stepST F_2479c D_2479c (Z_to_bv 64 pv) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      sn F_247a0 D_247a0.
      stepLD8 F_24618 D_24618 ret. stepLD8 F_2461c D_2461c s0v. stepLD8 F_24620 D_24620 s1v. stepLD8 F_24624 D_24624 s2v. stepLD8 F_24628 D_24628 s3v.
      zv F_2462c D_2462c (Z_to_bv 64 s). stepret F_24630 D_24630 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_B : forall regs m (pix pv : Z) (v : pixv),
    PIXat m pix v -> (4096 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24534) m rom) (mkst regs' (rl dVL_244bc 0x24550) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_d v) /\ getr regs' 11 = Z_to_bv 64 9 /\ getr regs' 13 = Z_to_bv 64 (p_d v)
      /\ getr regs' 19 = Z_to_bv 64 pv /\ getr regs' 9 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 13; 19]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m pix pv v PX Hpix AL8 H11 H12. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF).
    eexists. split.
    - stepb_ft F_24534 D_24534 ltac:(condZ).
      sn F_24538 D_24538. sn F_2453c D_2453c. sn F_24540 D_24540. sn F_24544 D_24544.
      stepb_ft F_24198 D_24198 ltac:(condZ).
      guard8 F_2419c D_2419c AL8. stepb_ft F_241a0 D_241a0 ltac:(condZ).
      stepLD F_241a4 D_241a4 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      stepretF F_241a8 D_241a8 F_24548.
      sn F_24548 D_24548. sn F_2454c D_2454c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P1 : forall regs m (dp : Z),
    (9 <= dp < 2 ^ 31)%Z ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24550) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_10563 0x10563 /\ getr regs' 11 = rl dVLS_103e0 0x103e0 /\ getr regs' 1 = rl dVL_244bc 0x246c8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_103e0 :: dVLS_10563 :: dVL_244bc :: nil).
    intros regs m dp Hdp Rg Rs H10 H11 H13. eexists. split.
    - stepb_ft F_24550 D_24550 ltac:(condZ).
      sn F_24554 D_24554.
      stepLD F_24558 D_24558 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_2455c D_2455c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_24560 D_24560. stepb_ft F_24564 D_24564 ltac:(condZ).
      sn F_24568 D_24568. sn F_2456c D_2456c. sn F_24570 D_24570. sn F_24574 D_24574. sn F_24578 D_24578. sn F_2457c D_2457c.
      sn F_246c4 D_246c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P2 : forall regs m (dp d' : Z),
    (0 <= dp <= 8)%Z -> (0 <= d' < dp)%Z ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp -> getr regs 8 = Z_to_bv 64 d' ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24550) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_10631 0x10631 /\ getr regs' 11 = rl dVLS_103e0 0x103e0 /\ getr regs' 1 = rl dVL_244bc 0x24690
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_103e0 :: dVLS_10631 :: dVL_244bc :: nil).
    intros regs m dp d' Hdp Hd Rg Rs H10 H11 H13 H8. eexists. split.
    - stepb_tk F_24550 D_24550 ltac:(condZ).
      sn F_246d0 D_246d0. stepb_ft F_246d4 D_246d4 ltac:(condZ).
      sn F_246d8 D_246d8. stepb_ft F_246dc D_246dc ltac:(condZ).
      sn F_246e0 D_246e0.
      stepLD F_246e4 D_246e4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_246e8 D_246e8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_246ec D_246ec. stepb_ft F_246f0 D_246f0 ltac:(condZ).
      sn F_246f4 D_246f4. sn F_246f8 D_246f8. sn F_246fc D_246fc. sn F_24700 D_24700. sn F_24704 D_24704.
      sn F_24658 D_24658. sn F_2465c D_2465c. sn F_24660 D_24660. sn F_2468c D_2468c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_D : forall regs m (cm dp d' : Z) (cv : cmapv),
    (dp = 1 \/ dp = 2 \/ dp = 4 \/ dp = 8)%Z -> (dp <= d' < 2 ^ 31)%Z -> CMAPat m cm cv -> (1 <= c_n cv)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 9 -> getr regs 13 = Z_to_bv 64 dp -> getr regs 8 = Z_to_bv 64 d' -> getr regs 18 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24550) m rom) (mkst regs' (rl dVL_244bc 0x24714) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (2 ^ dp) /\ getr regs' 12 = Z_to_bv 64 (c_n cv) /\ getr regs' 10 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 12; 13]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m cm dp d' cv Hdp Hd CM Hn H10 H11 H13 H8 H18. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepb_tk F_24550 D_24550 ltac:(condZ).
      sn F_246d0 D_246d0. stepb_ft F_246d4 D_246d4 ltac:(condZ).
      sn F_246d8 D_246d8. stepb_tk F_246dc D_246dc ltac:(condZ).
      stepLD F_24708 D_24708 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_2470c D_2470c ltac:(condZ).
      sn F_24710 D_24710. rewrite (sllw_1 _ Hdp).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P4 : forall regs m (k n : Z),
    (0 <= k < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 13 = Z_to_bv 64 k -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24714) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_107bc 0x107bc /\ getr regs' 11 = rl dVLS_103e0 0x103e0 /\ getr regs' 1 = rl dVL_244bc 0x24690
      /\ regs_agree (fun r => In r [1; 10; 11; 14]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_103e0 :: dVLS_107bc :: dVL_244bc :: nil).
    intros regs m k n Hk Hn Rg Rs H13 H12. eexists. split.
    - stepb_ft F_24714 D_24714 ltac:(condZ).
      sn F_24718 D_24718.
      stepLD F_2471c D_2471c (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_24720 D_24720 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_24724 D_24724. sn F_24728 D_24728. stepb_ft F_2472c D_2472c ltac:(condZ).
      sn F_24730 D_24730. sn F_24734 D_24734. sn F_24738 D_24738. sn F_2473c D_2473c. sn F_24740 D_24740.
      sn F_2468c D_2468c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_E : forall regs m (s pix k n : Z),
    (0 <= n <= k)%Z -> (k < 2 ^ 64)%Z -> (48 <= s)%Z ->
    getr regs 13 = Z_to_bv 64 k -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 9 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24714) m rom) (mkst regs' (rl dVL_24b70 0x24b70) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 (s - 44) /\ getr regs' 1 = rl dVL_244bc 0x24784
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m s pix k n Hn Hk Hs H13 H12 H2 H9. eexists. split.
    - stepb_tk F_24714 D_24714 ltac:(condZ).
      zv F_24778 D_24778 (Z_to_bv 64 (s - 44)). sn F_2477c D_2477c. sn F_24780 D_24780. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_G : forall regs m (s cm mx pv : Z) (cv : cmapv) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z -> ret_ok ret -> CMAPat m cm cv -> (0 <= mx < c_n cv)%Z -> (cm + 24 <= s - 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 mx) -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 18 = Z_to_bv 64 cm -> getr regs 19 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24784) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m s cm mx pv cv ret s0v s1v s2v s3v Hs Hpv Hpv64 Hret CM Hmx Hcm Rmx SOKp (R1 & R2 & R3 & R4 & R5) H2 H18 H19.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepLD F_24784 D_24784 (Z_to_le_bytes 4 mx) (Z_to_bv 64 mx) ltac:(addr_norm; exact Rmx) ltac:(apply lez4; lia).
      rewrite (v_lw_small mx) by lia.
      stepLD F_24788 D_24788 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      sn F_2478c D_2478c. stepb_ft F_24790 D_24790 ltac:(condZ).
      sn F_24794 D_24794. sn F_24798 D_24798.
      stepST F_2479c D_2479c (Z_to_bv 64 pv) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      sn F_247a0 D_247a0.
      stepLD8 F_24618 D_24618 ret. stepLD8 F_2461c D_2461c s0v. stepLD8 F_24620 D_24620 s1v. stepLD8 F_24624 D_24624 s2v. stepLD8 F_24628 D_24628 s3v.
      zv F_2462c D_2462c (Z_to_bv 64 s). stepret F_24630 D_24630 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_P5 : forall regs m (s cm mx : Z) (cv : cmapv),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> CMAPat m cm cv -> (c_n cv <= mx < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 mx) ->
    rdn SEGS m (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 18 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_244bc 0x24784) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_106a1 0x106a1 /\ getr regs' 11 = rl dVLS_103e0 0x103e0 /\ getr regs' 1 = rl dVL_244bc 0x24690
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: dVLS_103e0 :: dVLS_106a1 :: dVL_244bc :: nil).
    intros regs m s cm mx cv Hs Hs64 CM Hmx Rmx Rg Rs H2 H18. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF).
    eexists. split.
    - stepLD F_24784 D_24784 (Z_to_le_bytes 4 mx) (Z_to_bv 64 mx) ltac:(addr_norm; exact Rmx) ltac:(apply lez4; lia).
      rewrite (v_lw_small mx) by lia.
      stepLD F_24788 D_24788 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      sn F_2478c D_2478c. stepb_tk F_24790 D_24790 ltac:(condZ).
      sn F_247a4 D_247a4.
      stepLD F_247a8 D_247a8 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_247ac D_247ac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_247b0 D_247b0. sn F_247b4 D_247b4. stepb_ft F_247b8 D_247b8 ltac:(condZ).
      sn F_247bc D_247bc. sn F_247c0 D_247c0. sn F_247c4 D_247c4. sn F_247c8 D_247c8. sn F_247cc D_247cc.
      sn F_24688 D_24688. sn F_2468c D_2468c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_T : forall (pc : Z) regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (pc = (0x246c8 + dVL_244bc) \/ pc = (0x24690 + dVL_244bc))%Z -> (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pv_cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros pc regs m s ret s0v s1v s2v s3v Hpc Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2.
    destruct Hpc as [-> | ->]; eexists; split.
    - 
      sn F_246c8 D_246c8. sn F_246cc D_246cc.
      stepLD8 F_24618 D_24618 ret. stepLD8 F_2461c D_2461c s0v. stepLD8 F_24620 D_24620 s1v. stepLD8 F_24624 D_24624 s2v. stepLD8 F_24628 D_24628 s3v.
      zv F_2462c D_2462c (Z_to_bv 64 s). stepret F_24630 D_24630 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - 
      sn F_24690 D_24690. sn F_24694 D_24694.
      stepLD8 F_24618 D_24618 ret. stepLD8 F_2461c D_2461c s0v. stepLD8 F_24620 D_24620 s1v. stepLD8 F_24624 D_24624 s2v. stepLD8 F_24628 D_24628 s3v.
      zv F_2462c D_2462c (Z_to_bv 64 s). stepret F_24630 D_24630 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
Definition frame5 (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19)].

Lemma cells_FR5 : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR5 m s ret regs) (frame5 s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frame5, FR5. cbn [cellsZ]. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Definition cmap_ok (cv : cmapv) : Prop :=
  (c_d cv = 1 \/ c_d cv = 2 \/ c_d cv = 4 \/ c_d cv = 8)%Z /\ c_nalloc cv = (2 ^ c_d cv)%Z /\ (1 <= c_n cv <= c_nalloc cv)%Z /\ (1 <= c_arr cv)%Z.

(* [comment removed for export] *)
Definition pv_post (C : lctx) (A : AS) (s : Z) (m m' : word -> option byte) (pv valid : Z) : Prop :=
  POSTM C A s (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 valid))) m'.

(* [comment removed for export] *)
Lemma POSTM_store_same : forall C A s X M (a : word) bs0 bs,
  length bs0 = length bs -> (u a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  POSTM C A s (wbytes X a bs0) M -> POSTM C A s (wbytes X a bs) (wbytes M a bs).
Proof.
  intros C A s X M a bs0 bs Hlen Ha [F L]. split.
  - intros x N1 N2 N3 N4 N5.
    destruct (Z_lt_le_dec (u x) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; rewrite <- (wbytes_outside bs0 X a x) by lia; exact (F x N1 N2 N3 N4 N5)|].
    destruct (Z_lt_le_dec (u x) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. rewrite <- (wbytes_outside bs0 X a x) by lia. exact (F x N1 N2 N3 N4 N5).
  - intros q k i Lq Hi.
    destruct (Z_lt_le_dec (u (at_ q i)) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; rewrite <- (wbytes_outside bs0 X a (at_ q i)) by lia; exact (L q k i Lq Hi)|].
    destruct (Z_lt_le_dec (u (at_ q i)) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. rewrite <- (wbytes_outside bs0 X a (at_ q i)) by lia. exact (L q k i Lq Hi).
Qed.

Lemma POSTM_store_new : forall C A s X M (a : word) bs,
  (u a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  POSTM C A s X M -> POSTM C A s (wbytes X a bs) (wbytes M a bs).
Proof.
  intros C A s X M a bs Ha [F L]. split.
  - intros x N1 N2 N3 N4 N5.
    destruct (Z_lt_le_dec (u x) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; exact (F x N1 N2 N3 N4 N5)|].
    destruct (Z_lt_le_dec (u x) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. exact (F x N1 N2 N3 N4 N5).
  - intros q k i Lq Hi.
    destruct (Z_lt_le_dec (u (at_ q i)) (u a)) as [B|B]; [rewrite !wbytes_outside by lia; exact (L q k i Lq Hi)|].
    destruct (Z_lt_le_dec (u (at_ q i)) (u a + Z.of_nat (length bs))) as [B2|B2]; [rewrite !wbytes_inside by lia; reflexivity|].
    rewrite !wbytes_outside by lia. exact (L q k i Lq Hi).
Qed.

Theorem pixcmapIsValid_null_W : forall C A m md regs (s cm pv : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z -> (pv mod 4 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> pv_post C A s m m' pv 1 -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_244bc 0x244bc) m al_rom) md) S.
Proof. rl_dbounds (dVL_244bc :: nil).
  intros C A m md regs s cm pv cv ret S CK HW H2 Hs16 Hlo Hpv Hpvhi ALp H1 Hret H10 H11 H12 CM (Hd & Hna & Hn & Harr) Lcm HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *.
  pose proof CM as (Hc0 & Hc64 & CWF & _).
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  assert (ALc : (cm mod 8 = 0)%Z).
  { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & X & _). rewrite u_Z2bv in X by lia.
    rewrite <- (Z.add_0_r cm). apply mod16_plus_mod8; [exact X | reflexivity]. }
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pv 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKp.
  destruct (pv_A al_rom regs m s cm pv cv (Z_to_bv 64 0) ret ltac:(lia) Hpv ltac:(lia) CM Hd Hna Hn Harr ltac:(lia) ltac:(lia) ALc ALp SOK SOKp H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q8 & Q18 & Q13 & Q14 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1].
  set (M1 := wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) in RUN1 |- *.
  assert (HW2 : W C A M1 md) by (subst M1; apply (W_store_win C A _ md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
  assert (PM2 : pv_post C A s m M1 pv 0).
  { subst M1. apply POSTM_store_new; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | exact PM1]. }
  assert (CE1 : cellsZ M1 (frame5 s ret regs)).
  { subst M1. eapply (cellsZ_out _ _ pv (pv + 4)).
    - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
    - apply cells_FR5; lia. }
  unfold frame5 in CE1. cbn [cellsZ] in CE1. destruct CE1 as (C1 & C2 & C3 & C4 & C5 & _).
  destruct (pv_Z al_rom r1 M1 s pv ret _ _ _ _ ltac:(lia) Hpv ltac:(lia) Hret
              (W_sok_win C A M1 md pv 4 CK HW2 ltac:(lia) ltac:(cbn; lia))
              (conj C1 (conj C2 (conj C3 (conj C4 C5)))) Q2 Q11 Q12)
    as (r2 & RUN2 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN2 |].
  apply (HK _ r2).
  - apply (W_store_win C A _ md _ _ CK HW2); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
  - apply cs_kept_intro; csr; reflexivity.
  - eapply (POSTM_store_same C A s m M1); [| | exact PM2]; [rewrite !length_N_to_le_bytes; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - exact V10.
Qed.

Lemma str_pixcmapIsValid : str16 (0x103e0 + dVLS_103e0) 14. Proof. rl_dbounds (dVLS_103e0 :: nil). str16_tac. Qed.
Lemma str_pv_d8 : str16 (0x10563 + dVLS_10563) 30. Proof. rl_dbounds (dVLS_10563 :: nil). str16_tac. Qed.
Lemma str_pv_dd : str16 (0x10631 + dVLS_10631) 50. Proof. rl_dbounds (dVLS_10631 :: nil). str16_tac. Qed.
Lemma str_pv_ent : str16 (0x107bc + dVLS_107bc) 57. Proof. rl_dbounds (dVLS_107bc :: nil). str16_tac. Qed.
Lemma str_pv_max : str16 (0x106a1 + dVLS_106a1) 76. Proof. rl_dbounds (dVLS_106a1 :: nil). str16_tac. Qed.

#[local] Definition pv_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma pv_msg_W : forall C A m M md regs r (s pv fmt retpc : Z) kf (ret : word) (S : TSet),
  Cok C -> W C A M md -> pv_post C A s m M pv 0 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cellsZ M (frame5 s ret regs) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 retpc -> (retpc = (0x246c8 + dVL_244bc) \/ retpc = (0x24690 + dVL_244bc))%Z ->
  getr r 10 = Z_to_bv 64 fmt -> getr r 11 = rl dVLS_103e0 0x103e0 ->
  (forall x, In x pv_rest -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 LG) -> str16 fmt kf ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (rl dF_13694 0x13694) M al_rom) md) S.
Proof. rl_dbounds (dVLS_103e0 :: dVL_244bc :: nil).
  intros C A m M md regs r s pv fmt retpc kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 Hrp R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  assert (RETOK : ret_ok (Z_to_bv 64 retpc)) by (destruct Hrp as [-> | ->]; rl_ret_ok_VL).
  apply (lept_stderr1_W C A M md r (s - 48) fmt (0x103e0 + dVLS_103e0) kf 14 (Z_to_bv 64 retpc) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 RETOK
           R10 R11 Hin Sf str_pixcmapIsValid).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (PM2 : pv_post C A s m m2 pv 0).
  { eapply POSTM_trans; [exact PM|]. eapply (POSTM_range C A M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia]. }
  assert (CE2 : cellsZ m2 (frame5 s ret regs)).
  { eapply (cellsZ_out M m2 (s - 48 - 3376) (s - 48)); [exact OUT2 | | exact CE].
    unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  unfold frame5 in CE2. cbn [cellsZ] in CE2. destruct CE2 as (C1 & C2 & C3 & C4 & C5 & _).
  destruct (pv_T al_rom retpc r2 m2 s ret _ _ _ _ Hrp ltac:(lia) ltac:(lia) Hret (conj C1 (conj C2 (conj C3 (conj C4 C5)))) ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply (HK m2 r3 HW2).
  - apply cs_kept_intro; unfold pv_rest in RR; csr; reflexivity.
  - exists 0%Z. split; [lia|]. split; [exact PM2 | exact V10].
Qed.

Theorem pixcmapIsValid_pix_W : forall C A m md regs (s cm pix pv : Z) (cv : cmapv) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= pv)%Z -> (pv + 4 <= c_top C)%Z -> (pv mod 4 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 pv ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z ->
  dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     (exists valid, (valid = 0 \/ valid = 1)%Z /\ pv_post C A s m m' pv valid /\ getr regs' 10 = Z_to_bv 64 (1 - valid)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_244bc 0x244bc) m al_rom) md) S.
Proof. rl_dbounds (dVLS_10563 :: dVLS_10631 :: dVLS_106a1 :: dVLS_107bc :: dVL_244bc :: nil).
  intros C A m md regs s cm pix pv cv v ret S CK HW H2 Hs16 Hlo Hpv Hpvhi ALp H1 Hret H10 H11 H12 CM CMOK Lcm PX Lp DV Hw Hh Hwpl Ld HK.
  pose proof CMOK as (Hd & Hna & Hn & Harr).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
  pose proof (dval_range _ DV) as Hd32. pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as Hwr. rewrite <- Hwpl in Hwr.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  assert (ALc : (cm mod 8 = 0)%Z).
  { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & X & _). rewrite u_Z2bv in X by lia.
    rewrite <- (Z.add_0_r cm). apply mod16_plus_mod8; [exact X | reflexivity]. }
  assert (ALx : (pix mod 8 = 0)%Z).
  { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & X & _). rewrite u_Z2bv in X by lia.
    rewrite <- (Z.add_0_r pix). apply mod16_plus_mod8; [exact X | reflexivity]. }
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pv 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKp.
  destruct (pv_A al_rom regs m s cm pv cv (Z_to_bv 64 pix) ret ltac:(lia) Hpv ltac:(lia) CM Hd Hna Hn Harr ltac:(lia) ltac:(lia) ALc ALp SOK SOKp H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q8 & Q18 & Q13 & Q14 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1].
  set (M1 := wbytes (FR5 m s ret regs) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) in RUN1 |- *.
  assert (HW2 : W C A M1 md) by (subst M1; apply (W_store_win C A _ md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
  assert (PM2 : pv_post C A s m M1 pv 0).
  { subst M1. apply POSTM_store_new; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | exact PM1]. }
  assert (CE1 : cellsZ M1 (frame5 s ret regs)).
  { subst M1. eapply (cellsZ_out _ _ pv (pv + 4)).
    - intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
    - apply cells_FR5; lia. }
  assert (PX1 : PIXat M1 pix v).
  { subst M1. unfold FR5. repeat (apply PIXat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (CM1 : CMAPat M1 cm cv).
  { subst M1. unfold FR5. repeat (apply CMAPat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  assert (RR1 : forall x, In x pv_rest -> getr r1 x = getr regs x) by (unfold pv_rest; rest_solve).
  (* [comment removed for export] *)
  destruct (pv_B al_rom r1 M1 pix pv v PX1 Gp ALx Q11 Q12) as (r2 & RUN2 & V10 & V11 & V13 & V19 & V9 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN2 |].
  assert (RR2 : forall x, In x pv_rest -> getr r2 x = getr regs x) by (unfold pv_rest; rest_solve).
  destruct (Z_lt_ge_dec 8 (p_d v)) as [DBIG|DSMALL].
  { (* [comment removed for export] *)
    destruct (pv_P1 al_rom r2 M1 (p_d v) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) V10 V11 V13) as (r3 & RUN3 & U10 & U11 & U1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (pv_msg_W C A m M1 md regs r3 s pv (0x10563 + dVLS_10563) (0x246c8 + dVL_244bc) 30 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) U1 ltac:(left; reflexivity) U10 U11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_d8 HK H2). }
  assert (Hdp4 : (p_d v = 1 \/ p_d v = 2 \/ p_d v = 4 \/ p_d v = 8)%Z) by (unfold dval in DV; lia).
  assert (E8 : getr r2 8 = Z_to_bv 64 (c_d cv)) by (csr; reflexivity).
  pose proof (cf_d _ CWF) as Hcd. pose proof (cf_n _ CWF) as Hcn.
  destruct (Z_lt_ge_dec (c_d cv) (p_d v)) as [P2|Dok].
  { (* [comment removed for export] *)
    destruct (pv_P2 al_rom r2 M1 (p_d v) (c_d cv) ltac:(lia) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) V10 V11 V13 E8) as (r3 & RUN3 & U10 & U11 & U1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (pv_msg_W C A m M1 md regs r3 s pv (0x10631 + dVLS_10631) (0x24690 + dVL_244bc) 50 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) U1 ltac:(right; reflexivity) U10 U11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_dd HK H2). }
  assert (E18 : getr r2 18 = Z_to_bv 64 cm) by (csr; reflexivity).
  destruct (pv_D al_rom r2 M1 cm (p_d v) (c_d cv) cv Hdp4 ltac:(lia) CM1 ltac:(lia) V10 V11 V13 E8 E18) as (r3 & RUN3 & U13 & U12 & U10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (RR3 : forall x, In x pv_rest -> getr r3 x = getr regs x) by (unfold pv_rest; rest_solve).
  assert (Hpow : (2 <= 2 ^ p_d v <= 256)%Z) by (destruct Hdp4 as [E|[E|[E|E]]]; rewrite E; cbn; lia).
  destruct (Z_lt_ge_dec (2 ^ p_d v) (c_n cv)) as [P4|Nok].
  { (* [comment removed for export] *)
    destruct (pv_P4 al_rom r3 M1 (2 ^ p_d v) (c_n cv) ltac:(lia) ltac:(lia) (W_sev_got C A M1 md HW2) (W_sev C A M1 md HW2) U13 U12) as (r4 & RUN4 & Y10 & Y11 & Y1 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    apply (pv_msg_W C A m M1 md regs r4 s pv (0x107bc + dVLS_107bc) (0x24690 + dVL_244bc) 57 ret S CK HW2 PM2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE1
             ltac:(csr; reflexivity) Y1 ltac:(right; reflexivity) Y10 Y11 ltac:(unfold pv_rest; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_ent HK H2). }
  (* [comment removed for export] *)
  destruct (pv_E al_rom r3 M1 s pix (2 ^ p_d v) (c_n cv) ltac:(lia) ltac:(lia) ltac:(lia) U13 U12 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r4 & RUN4 & Y10 & Y11 & Y1 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  destruct (blk_rdn C A M1 md (Z_to_bv 64 (p_data v)) _ (p_data v) (Z.to_nat (4 * (p_wpl v * p_h v))) CK HW2 Ld ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as [rbs Hrbs].
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALpx & _). rewrite u_Z2bv in ALpx by lia.
  pose proof (W_sok_win C A M1 md (s - 48 - 128) 128 CK HW2 ltac:(lia) ltac:(cbn; lia)) as SOKf.
  pose proof (W_sok_win C A M1 md (s - 44) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as SOKq.
  pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd. pose proof (wf_wpl _ WF) as Rwpl.
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_maxindex (0x24b70 + dVL_24b70) 128) [pix; s - 44; p_w v; p_h v; p_d v; p_wpl v; p_data v]%Z r4 M1).
  { unfold SSP.spec_maxindex. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    rewrite Y10, Y11, Y2, Y1. rewrite !u_Z2bv by lia. rewrite !Z.add_0_r.
    split; [|split; [|split]].
    - split; [split; [reflexivity | lia]|]. split; [lia|].
      split; [split; [lia | rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALpx | reflexivity]]|].
      split; [split; [reflexivity | lia]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_w SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_h SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_d SEGS M1 pix v PX1)]]]|].
      split; [cbn [In]; lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_wpl SEGS M1 pix v PX1)]]]|].
      split; [rewrite Hwpl; reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (PIX_rd_data SEGS M1 pix v PX1)]]]|]. split; [lia|].
      split; [split; [lia | rewrite <- (Z.add_0_r (p_data v)); apply mod16_plus_mod4; [exact ALd | reflexivity]]|].
      split; [split; [unfold SSP.flatZ; lia | exists rbs; exact Hrbs]|]. split; [lia|].
      split; [split; [unfold SSP.flatZ; lia | exact SOKq]|].
      split; [split; [lia | replace (s - 44)%Z with (s + (-44))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]]|].
      split; [right; lia|].
      split; [split; [lia | rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity]|]. split; exact I.
    - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [exact SOKf|]. split; [cbn; lia|]. split; [unfold SSP.flatZ; cbn; lia | exact I].
    - split; [|exact I]. split; [left; cbn; lia|]. split; [left; cbn; lia|]. split; [left; cbn; lia|]. split; [left; cbn; lia|].
      split; [left; cbn; lia|]. split; [left; lia|]. split; [right; lia | exact I].
    - rl_ret_ok_VL. }
  pose proof (maxindex_contract (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [pix; s - 44; p_w v; p_h v; p_d v; p_wpl v; p_data v]%Z r4 M1 al_rom eq_refl PRE) as (outs & R' & M' & Hlen & RUN & POST).
  destruct outs as [|mx [|? ?]]; try discriminate Hlen. clear Hlen.
  unfold SSP.spec_maxindex in POST. SSP.spec_unfold_in POST.
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_maxindex app] in RUN, POST.
  destruct POST as (KEPT & _ & FRMx & GR & (_ & CELL & _) & Hmx & _).
  rewrite Y2, u_Z2bv in FRMx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul] in FRMx, CELL. rewrite !Z.add_0_r in FRMx, CELL.
  destruct CELL as [_ Rmx]. rewrite Z.mod_small in Rmx by lia.
  assert (OUT : forall x : word, ~ (s - 48 - 128 <= u x < s - 40)%Z -> M' x = M1 x).
  { intros x Hx. apply FRMx. split; [lia | split; [lia | exact I]]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (rl dVL_24b70 0x24b70) by (apply bv_eq; reflexivity) end. exact RUN. }
  rewrite Y1. 
  destruct KEPT as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & _).
  assert (HW3 : W C A M' md).
  { apply (W_mod_local C A M1 M' md CK HW2).
    - intros a Ha. left. unfold win. destruct (Z_lt_ge_dec (u a) (s - 48 - 128)); [exfalso; apply Ha; apply OUT; lia|].
      destruct (Z_lt_ge_dec (u a) (s - 40)); [lia|]. exfalso; apply Ha; apply OUT; lia.
    - exact GR.
    - intros a Ha. destruct (Z_lt_ge_dec (u a) (s - 48 - 128)); [rewrite OUT in Ha by lia; exact Ha|].
      destruct (Z_lt_ge_dec (u a) (s - 40)); [|rewrite OUT in Ha by lia; exact Ha]. apply (w_win _ _ _ _ HW2). unfold win. lia. }
  assert (PM3 : pv_post C A s m M' pv 0).
  { eapply POSTM_trans; [exact PM2|]. eapply (POSTM_range C A M1 md M'); [exact CK | exact HW2 | exact OUT | lia | lia | lia]. }
  assert (CE3 : cellsZ M' (frame5 s ret regs)).
  { eapply (cellsZ_out M1 M' (s - 48 - 128) (s - 40)); [exact OUT | | exact CE1].
    unfold frame5. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (CM3 : CMAPat M' cm cv) by (apply (CMAPat_frame M1 M' cm cv CM1); intros x Hx; apply OUT; lia).
  assert (Z2 : getr R' 2 = Z_to_bv 64 (s - 48)) by (rewrite K2; exact Y2).
  assert (Z18 : getr R' 18 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (Z19 : getr R' 19 = Z_to_bv 64 pv) by (csr; reflexivity).
  assert (RR4 : forall x, In x pv_rest -> getr r4 x = getr regs x) by (unfold pv_rest; rest_solve).
  destruct (Z_lt_ge_dec mx (c_n cv)) as [OKmx|BAD].
  - (* [comment removed for export] *)
    pose proof CE3 as CE4. unfold frame5 in CE4. cbn [cellsZ] in CE4. destruct CE4 as (C1 & C2 & C3 & C4 & C5 & _).
    destruct (pv_G al_rom R' M' s cm mx pv cv ret _ _ _ _ ltac:(lia) Hpv ltac:(lia) Hret CM3 ltac:(lia) ltac:(lia) Rmx
                (W_sok_win C A M' md pv 4 CK HW3 ltac:(lia) ltac:(cbn; lia)) (conj C1 (conj C2 (conj C3 (conj C4 C5)))) Z2 Z18 Z19)
      as (r5 & RUN5 & V2' & V1' & V10' & V8' & V9' & V18' & V19' & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK _ r5).
    + apply (W_store_win C A _ md _ _ CK HW3); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    + apply cs_kept_intro; unfold pv_rest in RR4; csr; reflexivity.
    + exists 1%Z. split; [lia|]. split; [| exact V10'].
      eapply (POSTM_store_same C A s m M'); [| | exact PM3]; [rewrite !length_N_to_le_bytes; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - (* [comment removed for export] *)
    destruct (pv_P5 al_rom R' M' s cm mx cv ltac:(lia) ltac:(lia) CM3 ltac:(lia) Rmx (W_sev_got C A M' md HW3) (W_sev C A M' md HW3) Z2 Z18)
      as (r5 & RUN5 & V10' & V11' & V1' & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (pv_msg_W C A m M' md regs r5 s pv (0x106a1 + dVLS_106a1) (0x24690 + dVL_244bc) 76 ret S CK HW3 PM3 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Hret CE3
             ltac:(csr; reflexivity) V1' ltac:(right; reflexivity) V10' V11' ltac:(unfold pv_rest in RR4 |- *; rest_solve)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right]); fail) str_pv_max HK H2).
Qed.



Section Segs2.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).

  Lemma sc_A : forall regs m (s pix cm : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_cmap v = 0%Z -> (1 <= pix)%Z -> (pix + 64 <= s - 48)%Z -> (1 <= cm < 2 ^ 64)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23ecc 0x23ecc) m rom)
                  (mkst regs' (rl dVL_244bc 0x244bc)
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                        (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                        (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                        (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = rl dVL_23ecc 0x23f24 /\ getr regs' 10 = Z_to_bv 64 cm
      /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 36)
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12]%list) regs regs'.
  Proof. rl_dbounds (dVL_244bc :: nil).
    intros regs m s pix cm v ret Hs Hs64 PX Hcm0 Hpix Hpixhi Hcm AL8 SOK SOKx H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - zv F_23ecc D_23ecc (Z_to_bv 64 (s - 48)).
      stepST F_23ed0 D_23ed0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_23ed4 D_23ed4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_23ed8 D_23ed8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_23edc D_23edc ltac:(condZ).
      stepb_ft F_23ee0 D_23ee0 ltac:(condZ).
      guard8 F_23ee4 D_23ee4 AL8. stepb_ft F_23ee8 D_23ee8 ltac:(condZ).
      stepLD F_23eec D_23eec (Z_to_le_bytes 8 (p_cmap v)) (Z_to_bv 64 (p_cmap v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      rewrite Hcm0.
      stepST F_23ef0 D_23ef0 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_23ef4 D_23ef4 ltac:(condZ).
      stepST F_23f10 D_23f10 (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 cm) ltac:(sok_in SOKx).
      zv F_23f14 D_23f14 (Z_to_bv 64 (s - 36)).
      sn F_23f18 D_23f18. sn F_23f1c D_23f1c.
      sn F_23f20 D_23f20. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_B : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23ecc 0x23f24) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret Rv R1 R2 R3 H2. eexists. split.
    - stepLD F_23f24 D_23f24 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_23f28 D_23f28 ltac:(condZ).
      sn F_23f2c D_23f2c. sn F_23f30 D_23f30.
      stepLD8 F_23fa4 D_23fa4 ret. stepLD8 F_23fa8 D_23fa8 s0v. stepLD8 F_23fac D_23fac s1v.
      zv F_23fb0 D_23fb0 (Z_to_bv 64 s). stepret F_23fb4 D_23fb4 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs2.

(* [comment removed for export] *)
Lemma POSTM_absorb : forall C Ar A M md m2 (s s' : Z) (a : word) bs, Cok C -> W C A M md -> sub_live Ar A ->
  (s' <= s)%Z -> (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z ->
  POSTM C A s' (wbytes M a bs) m2 -> POSTM C Ar s M m2.
Proof.
  intros C Ar A M md m2 s s' a bs CK HW SUB Hss Hlo Hhi Hs [F L]. pose proof CK as [T1 T2 T3 T4 T5]. laypins. split.
  - intros x N1 N2 N3 N4 N5. rewrite (F x N1 N2 N3 N4 ltac:(unfold scratch in *; lia)). apply wbytes_outside; [lia|]. unfold scratch in N5. lia.
  - intros q k i Lq Hi. pose proof (SUB q k Lq) as LqA. rewrite (L q k i LqA Hi).
    assert (RR : (u q <= u (at_ q i) < u q + k)%Z).
    { unfold at_. pose proof (alloc_top_lt (m_vmmaps md)) as AT. unfold two_pow_64 in AT.
      pose proof (ai_live_hull A M (m_vmmaps md) q k (w_inv _ _ _ _ HW) LqA) as (Hk0 & _ & TOP & _). pose proof (round16_ge k Hk0).
      rewrite u_Z2bv by (pose proof (u64_range q); lia). lia. }
    destruct (blk_byte C A M md q k (at_ q i) CK HW LqA RR) as (_ & _ & _ & NW & _).
    apply wbytes_outside; [lia|]. unfold win in NW. lia.
Qed.

Theorem pixSetColormap_W : forall C Ar A m md regs (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 cm ->
  PIXat m pix v -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live Ar (Z_to_bv 64 pix) = None -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  CMAPat m cm cv -> cmap_ok cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> Z_to_bv 64 pix <> Z_to_bv 64 cm ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix (set_cmap v cm) -> CMAPat m' cm cv -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_23ecc 0x23ecc) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix cm v cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX Hpc Lp LpR Lp0 CM CMOK Lcm NE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof CM as (Hc0 & Hc64 & CWF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  assert (ALx : (pix mod 8 = 0)%Z).
  { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & X & _). rewrite u_Z2bv in X by lia.
    rewrite <- (Z.add_0_r pix). apply mod16_plus_mod8; [exact X | reflexivity]. }
  assert (DISJ : (pix + 64 <= cm \/ cm + 24 <= pix)%Z).
  { destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lcm NE) as [X|X]; rewrite !u_Z2bv in X by lia;
      [left; pose proof (round16_ge 64 ltac:(lia)); lia | right; pose proof (round16_ge 24 ltac:(lia)); lia]. }
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKx : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix _ x PX ltac:(lia) E). }
  destruct (sc_A al_rom regs m s pix cm v ret ltac:(lia) ltac:(lia) PX Hpc ltac:(lia) ltac:(lia) ltac:(lia) ALx SOK SOKx H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) (Z_to_bv 64 (s - 32)) _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C Ar s m M0).
  { subst M0. wp_win CK. }
  destruct (WP_blk C Ar A m M0 md (Z_to_bv 64 pix) (Z_to_bv 64 (pix + 48)) 64 (word_to_le_bytes 8 (Z_to_bv 64 cm)) s CK WP0 Lp LpR Lp0 SUB
              ltac:(rewrite !u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia)) as [HW1 PM1].
  fold M1 in HW1, PM1. destruct WP0 as [HW0 PM0].
  assert (PX1 : PIXat M1 pix (set_cmap v cm)).
  { subst M1. apply PIX_wr_cmap; [|lia]. subst M0. repeat (apply PIXat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (CM1 : CMAPat M1 cm cv).
  { subst M1 M0. repeat (apply CMAPat_out; [|rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  apply (pixcmapIsValid_null_W C A M1 md r1 (s - 48) cm (s - 36) cv (rl dVL_23ecc 0x23f24) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (s - 36)%Z with (s + (-36))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]) Q1 ltac:(rl_ret_ok_VL) Q10 Q11 Q12 CM1 CMOK Lcm).
  intros m2 r2 HW2 CS2 PV2 A10.
  pose proof PV2 as [F2 L2].
  assert (Rv : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
  { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (CE : cellsZ m2 [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9)]).
  { apply (cellsZ_frm C (s - 48) _ m2 _ CK F2 ltac:(lia)); [repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil|].
    eapply (cellsZ_out M1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
      | repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil |].
    subst M1 M0. cbn [cellsZ]. repeat split; rdn_solve. }
  cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & _).
  destruct (sc_B al_rom r2 m2 s ret _ _ ltac:(lia) ltac:(lia) Hret Rv C1 C2 C3 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (EQb : forall (p n : Z) (x : word), live A (Z_to_bv 64 p) = Some n -> (0 <= p)%Z -> (p + n <= alloc_top (c_vm C))%Z ->
            (p <= u x < p + n)%Z -> m2 x = M1 x).
  { intros p n x L G0 TP Hx. pose proof (L2 (Z_to_bv 64 p) n (u x - p)%Z L ltac:(lia)) as E.
    replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
    rewrite E. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  apply (HK m2 r3 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    unshelve (eapply (POSTM_absorb C Ar A M1 md m2 s (s - 48) _ _ CK HW1 SUB ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
  - apply (PIXat_frame M1 m2 pix _ PX1). intros x Hx. exact (EQb pix 64%Z x Lp ltac:(lia) TOPp Hx).
  - apply (CMAPat_frame M1 m2 cm _ CM1). intros x Hx. exact (EQb cm 24%Z x Lcm ltac:(lia) TOPc Hx).
  - exact V10.
Qed.


End CmapValid.
