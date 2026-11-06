(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22Drv1.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22LeptStderr.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22LeptBase.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22CL7a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22CL8a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22CL9a.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22LeptCmapValid.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22LeptDeser.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22_code_13018_14000.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22_code_14000_15000.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22_code_15000_16000.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require LeptRoom.
Module O22LeptFuzz.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.pix1_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptArith2.
Import O22Drv1.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22LeptStderr.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22LeptBase.
Import O22CL7a.
Import O22CL8a.
Import O22CL9a.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22LeptCmapValid.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22LeptDeser.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22_code_13018_14000.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22_code_14000_15000.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22_code_15000_16000.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)








Import O22Drv1.O22FuzzIface.


Import O22CL7a.O22LeptErr.

Import O22CL8a.O22LeptCmap. Import O22CL8a.O22LeptPixHdr.

Import O22CL9a.O22LeptPixDestroy.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL22} {P16 : O22Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_A : forall regs m (s sz : Z) (dptr ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    store_ok SEGS m (Z_to_bv 64 0x1f848) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13684 : word) m rom)
                              (mkst regs' (0x14ce0 : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0x1f848) (word_to_le_bytes 8 (Z_to_bv 64 0x136e4))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x136b4 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13588 D_13588 (Z_to_bv 64 (s - 32)).
      stepST F_1358c D_1358c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13590 D_13590 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13594 D_13594 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13598 D_13598. sn F_1359c D_1359c. sn F_135a0 D_135a0. sn F_135a4 D_135a4. sn F_135a8 D_135a8.
      stepb_tk F_13708 D_13708 ltac:(condZ).
      sn F_13714 D_13714.
      stepST F_13718 D_13718 (Z_to_bv 64 0x1f848) (Z_to_bv 64 0x136e4) ltac:(store_ok_peel; exact SOKh).
      stepret F_1371c D_1371c (0x136a8 : word) ltac:(bveq).
      sn F_135ac D_135ac. sn F_135b0 D_135b0. sn F_135b4 D_135b4. sn F_14be0 D_14be0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x136b4 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_135b8 D_135b8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_135bc D_135bc ltac:(condZ).
      sn F_135d0 D_135d0.
      stepLD8 F_135d4 D_135d4 ret. stepLD8 F_135d8 D_135d8 s0v. stepLD8 F_135dc D_135dc s1v.
      zv F_135e0 D_135e0 (Z_to_bv 64 s). stepret F_135e4 D_135e4 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z) (v : pixv),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_rc v = 1%Z -> (1 <= p_data v)%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x136b4 : word) m rom)
       (mkst regs' (0x15c80 : word)
          (wbytes (wbytes (wbytes (wbytes (wbytes m
             (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
             (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x136c0)))
             (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 8)))
             (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 9)))
             (Z_to_bv 64 (pix + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 1 = Z_to_bv 64 0x136c4
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 PX Hrc Hdat Gp Hp SOK SOKp H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    eexists. split.
    - stepST F_135b8 D_135b8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_135bc D_135bc ltac:(condZ).
      sn F_135c0 D_135c0.
      (* [comment removed for export] *)
      zv F_13f60 D_13f60 (Z_to_bv 64 (s - 64)).
      stepST F_13f64 D_13f64 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0x136c0) ltac:(sok_in SOK).
      stepST F_13f68 D_13f68 (Z_to_bv 64 (s - 48)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13f6c D_13f6c (Z_to_bv 64 (s - 56)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_13f70 D_13f70 ltac:(condZ).
      stepfence F_13f74 D_13f74.
      stepLD F_13f78 D_13f78 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; repeat rdn_peel1; rewrite <- Hrc; exact (PIX_rd_rc SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      sn F_13f7c D_13f7c.
      stepfence F_13f80 D_13f80.
      stepb_ft F_13f84 D_13f84 ltac:(condZ).
      stepLD F_13f88 D_13f88 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_13f8c D_13f8c (Z_to_bv 64 (pix + 56)) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      sn F_13f90 D_13f90.
      sn F_14040 D_14040.
      stepLD8 F_14044 D_14044 (Z_to_bv 64 0x136c0). stepLD8 F_14048 D_14048 (getr regs 8). stepLD8 F_1404c D_1404c (getr regs 9).
      zv F_14050 D_14050 (Z_to_bv 64 (s - 32)). stepret F_14054 D_14054 (0x136c0 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_135c4 D_135c4.
      stepb_ft F_13720 D_13720 ltac:(condZ). sn F_13724 D_13724.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs', msteps SEGS (mkst regs (0x136c4 : word) m rom) (mkst regs' (0x13d2c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x136cc
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_135c8 D_135c8 (Z_to_bv 64 (s - 32)). sn F_135cc D_135cc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_D : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs', msteps SEGS (mkst regs (0x136cc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_135d0 D_135d0.
      stepLD8 F_135d4 D_135d4 ret. stepLD8 F_135d8 D_135d8 s0v. stepLD8 F_135dc D_135dc s1v.
      zv F_135e0 D_135e0 (Z_to_bv 64 s). stepret F_135e4 D_135e4 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End FuzzSegs.

Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL22} {P16 : O22Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_deser <= FUZZ_CALLS)%Z /\ (forall size, (0 <= size)%Z -> (RB_deser <= fuzz_margin size)%Z).
Proof. unfold RK_deser, RB_deser, FUZZ_CALLS, fuzz_margin. split; [lia | intros; lia]. Qed.

Theorem lept_fuzz_call : @fuzz_call_contract AL CL ASR.
Proof.
  unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret Hgp Htp Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm. pose proof (FZb size ltac:(lia)) as FZb'.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in Htp.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, A_EMPTY, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x13684) with (0x13684 : word) by (apply bv_eq; reflexivity).
  pose proof (u64_range (getr regs 2)) as Hs. pose proof (u64_range dptr) as Hdp. pose proof (u64_range sp0) as Hsp0r.
  set (s := u (getr regs 2)) in *.
  assert (H2 : getr regs 2 = Z_to_bv 64 s) by (subst s; rewrite zbv_self; reflexivity). clearbody s.
  set (dp := u dptr) in *.
  assert (Edp : dptr = Z_to_bv 64 dp) by (subst dp; rewrite zbv_self; reflexivity). clearbody dp. rewrite Edp in Ha0, Hlive, Hempty.
  set (C := LCTX sp0 argv envp s (m_vmmaps md) m A).
  assert (Etop : c_top C = s) by reflexivity. assert (Evm : c_vm C = m_vmmaps md) by reflexivity.
  assert (CK : Cok C) by (constructor; cbn; rewrite ?LSTK_val; lia).
  pose proof LSTK_val as LV.
  (* [comment removed for export] *)
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT3 : forall a : word, ~ (s - 32 <= u a < s)%Z -> FR3 m s ret regs a = m a).
  { intros a Ha. unfold FR3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (GR3 : mem_grows m (FR3 m s ret regs)) by (unfold FR3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x1f848) 8 = true) by exact Hhdl.
  destruct (fz_A al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FR3 m s ret regs) (Z_to_bv 64 0x1f848) (word_to_le_bytes 8 (Z_to_bv 64 0x136e4))) in *.
  assert (OUT1 : forall a : word, ~ (s - 32 <= u a < s)%Z -> ~ (0x1f848 <= u a < 0x1f850)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LL22] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 32)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x1f848); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0x1f850); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LL22]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  (* [comment removed for export] *)
  assert (Hdp1 : (1 <= dp < 2 ^ 64)%Z).
  { destruct (Z.eq_dec size 0) as [Z0|NZ].
    - destruct (Hempty Z0) as [E _]. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. lia.
    - pose proof (Hlive ltac:(lia)) as L. destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 L ltac:(lia)) as [G _]. rewrite u_Z2bv in G by lia. lia. }
  assert (HPL : (28 <= Z.of_nat (length pl))%Z -> payload C dp pl).
  { intros H28. assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
    destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
    split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KK : forall A' mf vm' rr, W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> POSTM C A s m1 mf -> aroom A' vm' (kR - FUZZ_CALLS) (bR - fuzz_margin size) -> realizes SEGS (mkCfg (mkst rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros A' mf vm' rr HWf LQ A0 CS [F L] HRf. apply (K A' mf vm' rr).
    - pose proof (w_inv _ _ _ _ HWf) as X. rewrite with_vmmaps_vmmaps in X. exact X.
    - exact LQ.
    - exact A0.
    - exact CS.
    - intros a N1 N2 N3 N4 N5. rewrite (F a); [apply OUT1; [lia | exact N4] | exact N1 | exact N2 | exact N3 | unfold hcell; cbn; exact N4 | unfold scratch; cbn; rewrite LV; lia].
    - intros q k i Lq Hi. rewrite (L q k i Lq Hi). destruct (BLK q k i Lq Hi) as [Ho NWq]. apply OUT1; [lia|]. intros R.
      destruct (ai_owned_where A m (m_vmmaps md) _ Hinv Ho) as [G|[[G _] _]].
      + apply pin_glob in G. cbn in G. unfold inZ in G. cbn in G. lia.
      + destruct (pin_grant _ G) as [X _]. apply X. unfold inZ; cbn. lia.
    - pose proof (w_def _ _ _ _ HWf) as D. exact D.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V1. exact V1.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V2. exact V2.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V3. exact V3.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V4. exact V4.
    - exact HRf. }
  apply (pixDeserialize_W C A m1 md r1 (s - 32) dp pl (Z_to_bv 64 0x136b4) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10
           ltac:(rewrite Q11, Hsz; reflexivity) Hdp1 ltac:(rewrite <- Hsz; lia) HPL
           kR bR Hrm ltac:(lia) ltac:(lia)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x136b4) with (0x136b4 : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (PMs : POSTM C A s m1 m') by (eapply POSTM_mono; [| exact PM']; lia).
  assert (C1 : rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) m1 m' (s - 8) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C2 : rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) m1 m' (s - 16) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C3 : rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) m1 m' (s - 24) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO)].
  - (* [comment removed for export] *)
    pose proof (W_sok_win C A' m' _ (s - 32) 32 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
    destruct (fz_B0 al_rom r2 m' s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret SOK' C1 C2 C3 Y2 A0) as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    assert (WPf : W C A' (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md) /\ POSTM C A s m1 (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
    { apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    destruct WPf as [HWf PMf].
    apply (KK A' _ vm' r3 HWf LQ V10 ltac:(apply cs_kept_intro; csr; reflexivity) PMf ltac:(room_tac)).
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
    destruct (blk_range C A' m' _ (Z_to_bv 64 (p_data v)) _ CK HW' Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    pose proof (W_sok_win C A' m' _ (s - 64) 64 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
    assert (SOKp : store_ok SEGS m' (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m' x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m' pix v x PX ltac:(lia) E). }
    destruct (fz_B1 al_rom r2 m' s pix v ltac:(lia) ltac:(lia) PX Rrc ltac:(lia) Gp ltac:(lia) SOK' SOKp Y2 A2p) as (r3 & RUN3 & V2 & V10 & V1 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (Ma := wbytes (wbytes (wbytes (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x136c0)))
                (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr r2 8))) (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr r2 9))).
    set (Mb := wbytes Ma (Z_to_bv 64 (pix + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WPa : W C A' Ma (with_vmmaps vm' md) /\ POSTM C A s m1 Ma).
    { subst Ma.
      do 3 (apply (WP_win C A' A m1 _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW') | rewrite u_Z2bv by lia; rewrite Etop, LV; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite Etop; lia]).
      apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    assert (WPb : W C A' Mb (with_vmmaps vm' md) /\ POSTM C A s m1 Mb).
    { subst Mb. apply (WP_blk C A A' m1 Ma _ (Z_to_bv 64 pix) _ 64 _ s CK WPa Lp LpA Lp0 (W_sub0 _ _ _ _ (proj1 WPa))); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
    destruct WPb as [HWb PMb].
    assert (OUTa : forall x : word, ~ (s - 56 <= u x < s - 24)%Z -> Ma x = m' x).
    { intros x Hx. subst Ma. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXb : PIXat Mb pix (set_data v 0)).
    { subst Mb. apply PIX_wr_data; [|lia]. apply (PIXat_frame m' Ma _ _ PX). intros x Hx. apply OUTa. lia. }
    assert (Y4 : getr r3 4 = Z_to_bv 64 0x2fba0) by (csr; reflexivity).
    (* [comment removed for export] *)
    replace (0x15c80 : word) with (Z_to_bv 64 0x15c80) by (apply bv_eq; reflexivity).
    apply (W_free16 C A' Mb _ r3 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x136c4) (4 * (p_wpl v * p_h v)) (s - 32) S CK HWb V10 Ld Ld0 V1
             ltac:(red; apply bv_eq; reflexivity) Y4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(rewrite Etop; lia)).
    intros A3 m3 vm3 r4 HWc CSc Lc LEQc PMc HRTc. rewrite with_vmmaps_twice in HWc |- *.
    replace (Z_to_bv 64 0x136c4) with (0x136c4 : word) by (apply bv_eq; reflexivity).
    pose proof PMc as [Fc Lc']. 
    assert (PMc' : POSTM C A s m1 m3).
    { eapply POSTM_trans; [exact PMb|]. apply (POSTM_sub C A A3).
      - intros q k Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 (p_data v))) as [->|NE]; [rewrite Lq in LdA; discriminate|]. rewrite (LEQc q NE). rewrite <- Lq.
        apply RQ; [intros ->; rewrite Lq in LpA; discriminate | exact NE |].
        intros NZ. destruct RC as [Z0|(_ & _ & _ & _ & _ & LcA & LaA & _)]; [lia|]. split; intros ->; [rewrite Lq in LcA | rewrite Lq in LaA]; discriminate.
      - eapply POSTM_mono; [|exact PMc]. lia. }
    assert (NEpd' : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zbv_ne; lia).
    assert (NEdp' : Z_to_bv 64 (p_data v) <> Z_to_bv 64 pix) by (apply zbv_ne; lia).
    assert (Lp3 : live A3 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQc _ NEpd'); exact Lp).
    assert (PX3 : PIXat m3 pix (set_data v 0)).
    { apply (PIXat_frame Mb m3 _ _ PXb). intros x Hx. pose proof (Lc' (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp3 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (Rpp : rdn SEGS m3 (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
    { rewrite (FRM_rdn16 C (s - 32) Mb m3 (s - 32) 8 CK Fc) by (rewrite ?Etop, ?LV; lia). subst Mb Ma. rewrite <- w2l_Z8 by lia. rdn_solve. }
    destruct (fz_C al_rom r4 m3 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r5 & RUN5 & Z2 & Z10 & Z1 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN5 |].
    apply (pixDestroy_W C A3 m3 _ r5 (s - 32) (s - 32) pix (p_cmap v) (4 * c_nalloc cv) 0 (set_data v 0) cv (Z_to_bv 64 0x136cc) S
             CK HWc Z2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
             Z1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Z10 Rpp PX3 ltac:(cbn; exact Rrc) ltac:(cbn; exact Rtx) ltac:(reflexivity) Lp3 Lp0).
    + left. reflexivity.
    + destruct RC as [Z0|(NZ & CM & Lcm & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [left; exact Z0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      assert (NEpc : Z_to_bv 64 pix <> Z_to_bv 64 (p_cmap v)) by (apply zbv_ne; lia).
      pose proof (live_apart C A' m' _ _ _ _ _ CK HW' Lp Lcm NEpc ltac:(lia) ltac:(lia)) as APc. rewrite !u_Z2bv in APc by lia.
      destruct (blk_range C A' m' _ (Z_to_bv 64 (p_cmap v)) 24 CK HW' Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
      pose proof (cf_arr _ (proj1 (proj2 (proj2 CM)))) as Rarr.
      destruct (blk_range C A' m' _ (Z_to_bv 64 (c_arr cv)) _ CK HW' La ltac:(lia)) as [Ga TOPa]. rewrite u_Z2bv in Ga, TOPa by lia.
      assert (NEcd' : Z_to_bv 64 (p_cmap v) <> Z_to_bv 64 (p_data v)) by (apply zbv_ne; lia).
      assert (NEad' : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 (p_data v)) by (apply zbv_ne; lia).
      assert (Lcm3 : live A3 (Z_to_bv 64 (p_cmap v)) = Some 24%Z) by (rewrite (LEQc _ NEcd'); exact Lcm).
      assert (La3 : live A3 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z) by (rewrite (LEQc _ NEad'); exact La).
      split; [| split; [exact Lcm3 | split; [exact La3 | split; [exact Lc0 | split; [exact La0 | split; [exact NEca | split; [exact NEcp | split; [exact NEap | exact Hna]]]]]]]].
      cbn [p_cmap set_data].
      apply (CMAPat_frame m' m3 _ _ CM). intros x Hx.
      pose proof (Lc' (Z_to_bv 64 (p_cmap v)) 24%Z (u x - p_cmap v)%Z Lcm3 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (p_cmap v + (u x - p_cmap v))%Z with (u x) in E by lia. rewrite zbv_self in E. rewrite E.
      subst Mb. rewrite wbytes_outside; [apply OUTa; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    + intros A4 mf vm4 r6 HWf CSf PDf PMd R0 HRTd. rewrite with_vmmaps_twice in HWf |- *.
      replace (Z_to_bv 64 0x136cc) with (0x136cc : word) by (apply bv_eq; reflexivity).
      pose proof PMd as [Fd Ld']. cbn [c_A0] in Ld'.
      assert (PMf : POSTM C A s m1 mf) by (eapply POSTM_trans; [exact PMc' | eapply POSTM_mono; [| exact PMd]; lia]).
      assert (D1 : rdn SEGS mf (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
      { rewrite (FRM_rdn16 C (s - 32 + 8) m3 mf (s - 8) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite (FRM_rdn16 C (s - 32) Mb m3 (s - 8) 8 CK Fc) by (rewrite ?Etop, ?LV; lia).
        rewrite <- C1. subst Mb. rewrite rdn_wbytes_out_Z; [| rewrite length_N_to_le_bytes; lia]. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
      assert (D2 : rdn SEGS mf (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
      { rewrite (FRM_rdn16 C (s - 32 + 8) m3 mf (s - 16) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite (FRM_rdn16 C (s - 32) Mb m3 (s - 16) 8 CK Fc) by (rewrite ?Etop, ?LV; lia).
        rewrite <- C2. subst Mb. rewrite rdn_wbytes_out_Z; [| rewrite length_N_to_le_bytes; lia]. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
      assert (D3 : rdn SEGS mf (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
      { rewrite (FRM_rdn16 C (s - 32 + 8) m3 mf (s - 24) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite (FRM_rdn16 C (s - 32) Mb m3 (s - 24) 8 CK Fc) by (rewrite ?Etop, ?LV; lia).
        rewrite <- C3. subst Mb. rewrite rdn_wbytes_out_Z; [| rewrite length_N_to_le_bytes; lia]. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
      destruct (fz_D al_rom r6 mf s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret D1 D2 D3 ltac:(csr; reflexivity)) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf)) | exact RUN7 |].
      apply (KK A4 mf vm4 r7 HWf).
      * intros q. cbn [p_data p_cmap set_data] in PDf. destruct PDf as (E1 & E2 & E3 & E4).
        destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|N1]; [rewrite E1, LpA; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 (p_data v))) as [->|N2].
        { rewrite (E4 _ NEdp' ltac:(intros X; exfalso; exact (X eq_refl))).
          2:{ intros NZ. destruct RC as [Z0|(_ & CM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NEdc & NEda)]; [lia|].
              pose proof CM as (Hc0 & Hc64 & _). pose proof (cf_arr _ (proj1 (proj2 (proj2 CM)))) as Rarr. split; apply zbv_ne; lia. }
          rewrite Lc, LdA. reflexivity. }
        destruct RC as [Z0|(NZ & CM & Lcm & La & Hna & LcA & LaA & REST)].
        -- rewrite (E4 q N1 ltac:(intros X; exfalso; exact (X eq_refl)) ltac:(intros X; exfalso; exact (X Z0))). rewrite (LEQc q N2). apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)].
        -- destruct (bv_eq_dec _ q (Z_to_bv 64 (p_cmap v))) as [->|N3]; [rewrite (proj1 (E3 ltac:(lia))), LcA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite (proj2 (E3 ltac:(lia))), LaA; reflexivity|].
           rewrite (E4 q N1 ltac:(intros X; exfalso; exact (X eq_refl)) ltac:(intros _; split; [exact N3 | exact N4])). rewrite (LEQc q N2). apply RQ; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]].
      * exact U10.
      * apply cs_kept_intro; csr; reflexivity.
      * exact PMf.
      * room_tac.
Qed.
End Final.
End O22LeptFuzz.

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22Kit.
Module O22LeptPinsI.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.pix1_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptDefs.
Import O22Kit.
Import O22Drv1.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22LeptBase.
Import O22LeptFuzz.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import O22Kit.O22MallocLayout.

Import O22Drv1.O22FuzzIface.



Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rdn_agree_on : forall segs (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x : word, a <= u x < a + Z.of_nat n -> M' x = M x) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros segs M M' a n Ha Hn E. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply E. lia.
Qed.

#[export] Instance s22_lept_pins : @LeptPins (@mallocng_alloc_layout LS22) LL22.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LL22 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LS22]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS22] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x4fe2b 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x4fe58 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LS22] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS22] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS22] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LS22] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS22] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS22] in H. lia.
  - intros r H. exact H.
  - reflexivity.
  - intros z Hz. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros z Hz. lia.
  - split; [lia|]. split; [lia|]. intros z Hz. lia.
  - lia.
Qed.

#[export] Instance s22_pins16 : @O22Pins (@mallocng_alloc_layout LS22) (@mallocng_calloc_layout LS22).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s22_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LS22) (@mallocng_calloc_layout LS22),
  @fuzz_call_contract (@mallocng_alloc_layout LS22) (@mallocng_calloc_layout LS22) ASR.
Proof. intros ASR. exact (@lept_fuzz_call _ _ ASR s22_lept_pins s22_pins16). Qed.
End O22LeptPinsI.

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require O22Main.
Module O22Pins.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.pix1_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import O22Kit.
Import O22Drv1.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import O22Kit.O22MallocLayout. Import O22Kit.O22Startup. Import O22Kit.O22StartupDefs. Import O22Kit.O22StartupFacts.

Import O22Drv1.O22MainEntry. Import O22Drv1.O22Open. Import O22Drv1.O22Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x4fe2b) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s22_pins : @O22Main.pins (@mallocng_alloc_layout LS22).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS22] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS22] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS22] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS22] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS22] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x2fad0 <= a)%Z -> (a + Z.of_nat n <= 0x4fe98)%Z -> (a + Z.of_nat n <= 0x2fafc \/ 0x2fb00 <= a)%Z ->
              (a + Z.of_nat n <= 0x4fbe0 \/ 0x4fe00 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS22].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x4fe2b) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x4fe2b%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x4fe2b%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x4fe2b) + Z.of_nat 0)%Z with 0x4fe2b%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x4fe58%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS22]. change (bv_unsigned (Z_to_bv 64 0x4fe28) + 8)%Z with 0x4fe30%Z.
        rewrite (LIBC 0x4fe30%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x1e800)) with 0x1e800%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End O22Pins.

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Spec.
Module O22Closed.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.pix1_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver.Spec.
Import O22Kit.
Import O22Pins.
Import O22Drv1.
Import O22LeptPinsI.
Import OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22.O22Main.
(* [comment removed for export] *)







Import O22Kit.O22MallocLayout. Import O22Kit.O22Alloc. Import O22Kit.O22Sure.


Import O22Drv1.O22FuzzIface.

Import ListNotations.

Theorem s22_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Plain.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@O22Main.ref_realizes_spec_pins _ _ s22_sure O22Pins.s22_pins (s22_fuzz_call s22_sure)).
Qed.
End O22Closed.
