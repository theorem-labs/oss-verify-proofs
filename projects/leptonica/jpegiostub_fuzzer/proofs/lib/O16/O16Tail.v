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
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16Drv1.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptStderr.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16CL7a.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16CL8a.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16CL9a.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptCmapValid.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16LeptDeser.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16_code_13010_14000.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16_code_14000_15000.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require LeptRoom.
Module O16LeptFuzz.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptArith2.
Import O16Drv1.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptStderr.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16CL7a.
Import O16CL8a.
Import O16CL9a.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptCmapValid.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptDeser.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16_code_13010_14000.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16_code_14000_15000.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)








Import O16Drv1.O16FuzzIface.


Import O16CL7a.O16LeptErr.

Import O16CL8a.O16LeptCmap. Import O16CL8a.O16LeptPixHdr.

Import O16CL9a.O16LeptPixDestroy.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x1367c : word) m rom) (mkst regs' ret (FR3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13580 D_13580 (Z_to_bv 64 (s - 32)).
      stepST F_13584 D_13584 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13588 D_13588 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1358c D_1358c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13590 D_13590. sn F_13594 D_13594. stepb_tk F_13598 D_13598 ltac:(condZ).
      sn F_135d0 D_135d0.
      stepLD8 F_135d4 D_135d4 ret. stepLD8 F_135d8 D_135d8 (getr regs 8). stepLD8 F_135dc D_135dc (getr regs 9).
      zv F_135e0 D_135e0 (Z_to_bv 64 s). stepret F_135e4 D_135e4 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_big : forall regs m (s sz : Z) (dptr ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    store_ok SEGS m (Z_to_bv 64 0x1f7f8) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x1367c : word) m rom)
                              (mkst regs' (0x14c90 : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0x1f7f8) (word_to_le_bytes 8 (Z_to_bv 64 0x136e4))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x136b4 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13580 D_13580 (Z_to_bv 64 (s - 32)).
      stepST F_13584 D_13584 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13588 D_13588 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1358c D_1358c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13590 D_13590. sn F_13594 D_13594. stepb_ft F_13598 D_13598 ltac:(condZ).
      sn F_1359c D_1359c. sn F_135a0 D_135a0. sn F_135a4 D_135a4. sn F_135a8 D_135a8.
      stepb_tk F_13708 D_13708 ltac:(condZ).
      sn F_13714 D_13714.
      stepST F_13718 D_13718 (Z_to_bv 64 0x1f7f8) (Z_to_bv 64 0x136e4) ltac:(store_ok_peel; exact SOKh).
      stepret F_1371c D_1371c (0x136a8 : word) ltac:(bveq).
      sn F_135ac D_135ac. sn F_135b0 D_135b0. sn F_135b4 D_135b4. sn F_14b90 D_14b90. apply mst_refl.
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
  Lemma fz_B1 : forall regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x136b4 : word) m rom)
       (mkst regs' (0x13d20 : word)
          (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
                     (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x136c4)))
                  (Z_to_bv 64 (pix + 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x136cc
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Gp Hp SOK SOKp H2 H10. eexists. split.
    - stepST F_135b8 D_135b8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_135bc D_135bc ltac:(condZ).
      sn F_135c0 D_135c0. sn F_135c4 D_135c4.
      zv F_14b24 D_14b24 (Z_to_bv 64 (s - 48)).
      stepST F_14b28 D_14b28 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0x136c4) ltac:(sok_in SOK).
      stepb_ft F_14b2c D_14b2c ltac:(condZ). stepb_tk F_14b30 D_14b30 ltac:(condZ).
      sn F_14b70 D_14b70. sn F_14b74 D_14b74.
      stepb_ft F_13f54 D_13f54 ltac:(condZ). sn F_13f58 D_13f58. sn F_13f5c D_13f5c.
      stepST F_13f60 D_13f60 (Z_to_bv 64 (pix + 36)) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      stepret F_13f64 D_13f64 (0x14c74 : word) ltac:(bveq).
      sn F_14b78 D_14b78. sn F_14b7c D_14b7c.
      stepLD8 F_14b84 D_14b84 (Z_to_bv 64 0x136c4).
      zv F_14b88 D_14b88 (Z_to_bv 64 (s - 32)). stepret F_14b8c D_14b8c (0x136c4 : word) ltac:(bveq).
      zv F_135c8 D_135c8 (Z_to_bv 64 (s - 32)). sn F_135cc D_135cc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s : Z) (ret s0v s1v : word),
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
Context {PINS : @LeptPins AL LL16} {P16 : O16Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

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
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x1367c) with (0x1367c : word) by (apply bv_eq; reflexivity).
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
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K A (FR3 m s ret regs) (m_vmmaps md) r1).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 32)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - apply cs_kept_intro; csr; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - room_tac. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 129016) 8 = true) by exact Hhdl.
  destruct (fz_big al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FR3 m s ret regs) (Z_to_bv 64 129016) (word_to_le_bytes 8 (Z_to_bv 64 79588))) in *.
  assert (OUT1 : forall a : word, ~ (s - 32 <= u a < s)%Z -> ~ (129016 <= u a < 129024)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LL16] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 32)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 129016); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 129024); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LL16]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
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
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia)
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
    pose proof (W_sok_win C A' m' _ (s - 48) 48 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
    assert (SOKp : store_ok SEGS m' (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m' x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m' pix v x PX ltac:(lia) E). }
    destruct (fz_B1 al_rom r2 m' s pix ltac:(lia) ltac:(lia) Gp ltac:(lia) SOK' SOKp Y2 A2p) as (r3 & RUN3 & V2 & V10 & V1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (Ma := wbytes (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x136c4))).
    set (Mb := wbytes Ma (Z_to_bv 64 (pix + 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))).
    assert (WPa : W C A' Ma (with_vmmaps vm' md) /\ POSTM C A s m1 Ma).
    { subst Ma. apply (WP_win C A' A m1 _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW') | rewrite u_Z2bv by lia; rewrite Etop, LV; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite Etop; lia].
      apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    assert (WPb : W C A' Mb (with_vmmaps vm' md) /\ POSTM C A s m1 Mb).
    { subst Mb. apply (WP_blk C A A' m1 Ma _ (Z_to_bv 64 pix) _ 64 _ s CK WPa Lp LpA Lp0 (W_sub0 _ _ _ _ (proj1 WPa))); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
    destruct WPb as [HWb PMb].
    assert (OUTa : forall x : word, ~ (s - 40 <= u x < s - 24)%Z -> Ma x = m' x).
    { intros x Hx. subst Ma. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXb : PIXat Mb pix (set_spec v 1)).
    { subst Mb. apply PIX_wr_spec; [|lia]. apply (PIXat_frame m' Ma _ _ PX). intros x Hx. apply OUTa. lia. }
    assert (Rpp : rdn SEGS Mb (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
    { subst Mb Ma. rewrite <- w2l_Z8 by lia. rdn_solve. }
    apply (pixDestroy_W C A' Mb _ r3 (s - 32) (s - 32) pix (p_cmap v) (4 * c_nalloc cv) (4 * (p_wpl v * p_h v)) (set_spec v 1) cv (Z_to_bv 64 0x136cc) S
             CK HWb V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
             V1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) V10 Rpp PXb ltac:(cbn; exact Rrc) ltac:(cbn; exact Rtx) ltac:(reflexivity) Lp Lp0).
    + right. cbn [p_data set_spec]. split; [exact Ld | split; [exact Ld0 | split; [lia | split; [exact NEdp |]]]].
      intros NZ. destruct RC as [Z0|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NEdc & NEda)]; [lia|]. split; [exact NEdc | exact NEda].
    + destruct RC as [Z0|(NZ & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [left; exact Z0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      assert (NEpc : Z_to_bv 64 pix <> Z_to_bv 64 (p_cmap v)) by (apply zbv_ne; lia).
      pose proof (live_apart C A' m' _ _ _ _ _ CK HW' Lp Lc NEpc ltac:(lia) ltac:(lia)) as APc. rewrite !u_Z2bv in APc by lia.
      destruct (blk_range C A' m' _ (Z_to_bv 64 (p_cmap v)) 24 CK HW' Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
      split; [| split; [exact Lc | split; [exact La | split; [exact Lc0 | split; [exact La0 | split; [exact NEca | split; [exact NEcp | split; [exact NEap | exact Hna]]]]]]]].
      apply (CMAPat_frame m' Mb _ _ CM). intros x Hx. subst Mb. rewrite wbytes_outside; [apply OUTa; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    + intros A'' mf vm'' r4 HWf CSf PDf PMd R0 HRTd. rewrite with_vmmaps_twice in HWf |- *.
      replace (Z_to_bv 64 0x136cc) with (0x136cc : word) by (apply bv_eq; reflexivity).
      pose proof PMd as [Fd Ld']. cbn [c_A0] in Ld'.
      assert (PMf : POSTM C A s m1 mf) by (eapply POSTM_trans; [exact PMb | eapply POSTM_mono; [| exact PMd]; lia]).
      assert (OUTb : forall x : word, ~ (s - 40 <= u x < s - 24)%Z -> ~ (pix + 36 <= u x < pix + 40)%Z -> Mb x = m' x).
      { intros x H1x H2x. subst Mb. rewrite wbytes_outside; [apply OUTa; exact H1x | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
      assert (D1 : rdn SEGS mf (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
      { rewrite (FRM_rdn16 C (s - 32 + 8) Mb mf (s - 8) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia. }
      assert (D2 : rdn SEGS mf (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
      { rewrite (FRM_rdn16 C (s - 32 + 8) Mb mf (s - 16) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia. }
      assert (D3 : rdn SEGS mf (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
      { rewrite (FRM_rdn16 C (s - 32 + 8) Mb mf (s - 24) 8 CK Fd) by (rewrite ?Etop, ?LV; lia). rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia. }
      destruct (fz_C al_rom r4 mf s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret D1 D2 D3 ltac:(csr; reflexivity)) as (r5 & RUN5 & U2 & U1 & U10 & U8 & U9 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWf)) | exact (mp_lazy _ (w_pure _ _ _ _ HWf)) | exact RUN5 |].
      apply (KK A'' mf vm'' r5 HWf).
      * intros q. cbn [p_data set_spec] in PDf. destruct PDf as (E1 & E2 & E3 & E4).
        destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|N1]; [rewrite E1, LpA; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 (p_data v))) as [->|N2]; [rewrite (E2 ltac:(lia)), LdA; reflexivity|].
        destruct RC as [Z0|(NZ & CM & Lc & La & Hna & LcA & LaA & REST)].
        -- rewrite (E4 q N1 ltac:(intros _; exact N2) ltac:(intros X; exfalso; exact (X Z0))). apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)].
        -- destruct (bv_eq_dec _ q (Z_to_bv 64 (p_cmap v))) as [->|N3]; [rewrite (proj1 (E3 ltac:(lia))), LcA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite (proj2 (E3 ltac:(lia))), LaA; reflexivity|].
           rewrite (E4 q N1 ltac:(intros _; exact N2) ltac:(intros _; split; [exact N3 | exact N4])). apply RQ; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]].
      * exact U10.
      * apply cs_kept_intro; csr; reflexivity.
      * exact PMf.
      * room_tac.
Qed.
End Final.
End O16LeptFuzz.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16Kit.
Module O16LeptPinsI.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptDefs.
Import O16Kit.
Import O16Drv1.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16LeptBase.
Import O16LeptFuzz.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)







Import O16Kit.O16MallocLayout.

Import O16Drv1.O16FuzzIface.



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

#[export] Instance s16_lept_pins : @LeptPins (@mallocng_alloc_layout LS16) LL16.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LL16 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LS16]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x4fddb 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x4fe08 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LS16] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LS16] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
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

#[export] Instance s16_pins16 : @O16Pins (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s16_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16),
  @fuzz_call_contract (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16) ASR.
Proof. intros ASR. exact (@lept_fuzz_call _ _ ASR s16_lept_pins s16_pins16). Qed.
End O16LeptPinsI.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require O16Main.
Module O16Pins.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import O16Kit.
Import O16Drv1.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16Main.
(* [comment removed for export] *)







Import O16Kit.O16MallocLayout. Import O16Kit.O16Startup. Import O16Kit.O16StartupDefs. Import O16Kit.O16StartupFacts.

Import O16Drv1.O16MainEntry. Import O16Drv1.O16Open. Import O16Drv1.O16Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x4fddb) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s16_pins : @O16Main.pins (@mallocng_alloc_layout LS16).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS16] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x2fa80 <= a)%Z -> (a + Z.of_nat n <= 0x4fe48)%Z -> (a + Z.of_nat n <= 0x2faac \/ 0x2fab0 <= a)%Z ->
              (a + Z.of_nat n <= 0x4fb90 \/ 0x4fdb0 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x4fddb) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x4fddb%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x4fddb%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x4fddb) + Z.of_nat 0)%Z with 0x4fddb%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x4fe08%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS16]. change (bv_unsigned (Z_to_bv 64 0x4fdd8) + 8)%Z with 0x4fde0%Z.
        rewrite (LIBC 0x4fde0%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x1e7b0)) with 0x1e7b0%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End O16Pins.

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Spec.
Module O16Closed.
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
Import OSSVerify.leptonica.jpegiostub_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver.Spec.
Import O16Kit.
Import O16Pins.
Import O16Drv1.
Import O16LeptPinsI.
Import OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16.O16Main.
(* [comment removed for export] *)







Import O16Kit.O16MallocLayout. Import O16Kit.O16Alloc. Import O16Kit.O16Sure.


Import O16Drv1.O16FuzzIface.

Import ListNotations.

Theorem s16_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Plain.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@O16Main.ref_realizes_spec_pins _ _ s16_sure O16Pins.s16_pins (s16_fuzz_call s16_sure)).
Qed.
End O16Closed.
