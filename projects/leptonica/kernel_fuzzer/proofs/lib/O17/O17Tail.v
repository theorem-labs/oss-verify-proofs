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
From OSSVerify.leptonica.kernel_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require FPSteps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17Drv1.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptStderr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17CL7a.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptCmap.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptPixDestroy.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptPixHdr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptCmapValid.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptDeser.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernSegs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernC2d.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernCreate.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernDestroy.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernFromPix.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17LeptKernFromPixB.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_132e8_14000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_14000_15000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17_code_15000_16000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptRoomK.
Module O17LeptFuzz.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith2.
Import O17Drv1.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptBase.
Import O17CL7a.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptCmap.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptPixDestroy.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptPixHdr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptCmapValid.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptDeser.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernSegs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernC2d.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernCreate.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernDestroy.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernFromPix.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptKernFromPixB.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_132e8_14000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_14000_15000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17_code_15000_16000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptRoomK.
(* [comment removed for export] *)








Import O17Drv1.O17FuzzIface.


Import O17CL7a.O17LeptErr. Import O17CL7a.O17LeptKernSegs2.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13954 : word) m rom) (mkst regs' ret (FR3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13858 D_13858 (Z_to_bv 64 (s - 48)).
      stepST F_1385c D_1385c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13860 D_13860 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13864 D_13864 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13868 D_13868. sn F_1386c D_1386c. stepb_tk F_13870 D_13870 ltac:(condZ).
      sn F_138b8 D_138b8.
      stepLD8 F_138bc D_138bc ret. stepLD8 F_138c0 D_138c0 (getr regs 8). stepLD8 F_138c4 D_138c4 (getr regs 9).
      zv F_138c8 D_138c8 (Z_to_bv 64 s). stepret F_138cc D_138cc ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_big : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0x201c8) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13954 : word) m rom)
                              (mkst regs' (0x150dc : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0x201c8) (word_to_le_bytes 8 (Z_to_bv 64 0x139cc))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1398c /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13858 D_13858 (Z_to_bv 64 (s - 48)).
      stepST F_1385c D_1385c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13860 D_13860 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13864 D_13864 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13868 D_13868. sn F_1386c D_1386c. stepb_ft F_13870 D_13870 ltac:(condZ).
      sn F_13874 D_13874. sn F_13878 D_13878. sn F_1387c D_1387c. sn F_13880 D_13880.
      stepb_tk F_139f0 D_139f0 ltac:(condZ).
      sn F_139fc D_139fc.
      stepST F_13a00 D_13a00 (Z_to_bv 64 0x201c8) (Z_to_bv 64 0x139cc) ltac:(store_ok_peel; exact SOKh).
      stepret F_13a04 D_13a04 (0x13980 : word) ltac:(bveq).
      sn F_13884 D_13884. sn F_13888 D_13888. sn F_1388c D_1388c. sn F_14fdc D_14fdc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1398c : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_13890 D_13890 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_13894 D_13894 ltac:(condZ).
      sn F_138b8 D_138b8.
      stepLD8 F_138bc D_138bc ret. stepLD8 F_138c0 D_138c0 s0v. stepLD8 F_138c4 D_138c4 s1v.
      zv F_138c8 D_138c8 (Z_to_bv 64 s). stepret F_138cc D_138cc ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x1398c : word) m rom)
       (mkst regs' (0x158e8 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x139a0 /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 11 = Z_to_bv 64 2 /\ getr regs' 12 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Hp SOK H2 H10. eexists. split.
    - stepST F_13890 D_13890 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_13894 D_13894 ltac:(condZ).
      sn F_13898 D_13898. sn F_1389c D_1389c. sn F_138a0 D_138a0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s : Z) (kel : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = kel ->
    exists regs', msteps SEGS (mkst regs (0x139a0 : word) m rom)
       (mkst regs' (0x14008 : word) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 kel)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x139ac /\ getr regs' 10 = Z_to_bv 64 (s - 32)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s kel Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_138a4 D_138a4 (Z_to_bv 64 (s - 40)) kel ltac:(sok_in SOK).
      zv F_138a8 D_138a8 (Z_to_bv 64 (s - 32)). sn F_138ac D_138ac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_D : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x139ac : word) m rom) (mkst regs' (0x1574c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x139b4 /\ getr regs' 10 = Z_to_bv 64 (s - 40)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_138b0 D_138b0 (Z_to_bv 64 (s - 40)). sn F_138b4 D_138b4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x139b4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_138b8 D_138b8.
      stepLD8 F_138bc D_138bc ret. stepLD8 F_138c0 D_138c0 s0v. stepLD8 F_138c4 D_138c4 s1v.
      zv F_138c8 D_138c8 (Z_to_bv 64 s). stepret F_138cc D_138cc ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End FuzzSegs.

Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma ex_range_dec : forall (P : Z -> Prop), (forall i, {P i} + {~ P i}) ->
  forall (n : nat) (lo : Z), {i | (lo <= i < lo + Z.of_nat n)%Z /\ P i} + {forall i, (lo <= i < lo + Z.of_nat n)%Z -> ~ P i}.
Proof.
  intros P D n. induction n as [|n IH]; intros lo.
  - right. intros i Hi. lia.
  - destruct (D lo) as [Y|N]; [left; exists lo; split; [lia | exact Y]|].
    destruct (IH (lo + 1)%Z) as [(i & Hi & Y)|N'].
    + left. exists i. split; [lia | exact Y].
    + right. intros i Hi. destruct (Z.eq_dec i lo) as [->|NE]; [exact N|]. apply N'. lia.
Qed.

(* [comment removed for export] *)
Lemma fuzz_covers : forall v : pixv, pshape v ->
  (0 <= RK_kfp (p_d v) (p_h v))%Z /\ (0 <= RB_kfp (p_d v) (p_h v) (p_w v))%Z /\
  (RK_deser + RK_kfp (p_d v) (p_h v) <= FUZZ_CALLS)%Z /\ (forall size, (RB_deser + RB_kfp (p_d v) (p_h v) (p_w v) <= fuzz_margin size)%Z).
Proof.
  intros v (Hw1 & Hh1 & (DV & Hw2 & Hh2 & Hsz) & Ewpl).
  assert (H8 : p_d v = 8%Z -> (p_w v * p_h v <= 2 ^ 26)%Z).
  { intros E. rewrite E in Hsz. pose proof (wpl8_ge (p_w v) ltac:(lia)). nia. }
  destruct (kfp_cost_bound (p_d v) (p_h v) (p_w v) ltac:(lia) ltac:(lia) H8) as [[K0 K1] [B0 B1]].
  unfold RK_deser, RB_deser, FUZZ_CALLS, fuzz_margin. repeat split; try lia.
Qed.

Theorem lept_fuzz_call : @fuzz_call_contract AL CL acr_sure.
Proof.
  unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hz Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret Hgp Htp Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof (fuzz_margin_bound size ltac:(lia)) as FZm.
  assert (FZd : (RK_deser <= FUZZ_CALLS)%Z /\ (RB_deser <= fuzz_margin size)%Z) by (unfold RK_deser, RB_deser, FUZZ_CALLS, fuzz_margin; lia).
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in Htp.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, A_EMPTY, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x13954) with (0x13954 : word) by (apply bv_eq; reflexivity).
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
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT3 : forall a : word, ~ (s - 48 <= u a < s)%Z -> FR3 m s ret regs a = m a).
  { intros a Ha. unfold FR3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (GR3 : mem_grows m (FR3 m s ret regs)) by (unfold FR3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K fx A (FR3 m s ret regs) (m_vmmaps md) r1 Hz).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 48)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - apply cs_kept_intro; csr; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - apply (aroom_mono _ _ _ _ _ _ Hrm); lia. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x201c8) 8 = true) by exact Hhdl.
  destruct (fz_big al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FR3 m s ret regs) (Z_to_bv 64 0x201c8) (word_to_le_bytes 8 (Z_to_bv 64 0x139cc))) in *.
  assert (OUT1 : forall a : word, ~ (s - 48 <= u a < s)%Z -> ~ (0x201c8 <= u a < 0x201d0)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LL17] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 48)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x201c8); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0x201d0); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LL17]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KK : forall (fx' : FPState) A' mf vm' rr, frm_zero (@fp_csr fx') -> W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> POSTM C A s m1 mf -> aroom A' vm' (kR - FUZZ_CALLS) (bR - fuzz_margin size) -> realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros fx' A' mf vm' rr Hz' HWf LQ A0 CS [F L] HRf. apply (K fx' A' mf vm' rr Hz').
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
  apply (pixDeserialize_W C A m1 md r1 (s - 48) dp pl (Z_to_bv 64 0x1398c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia)
           kR bR Hrm ltac:(lia) ltac:(lia)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x1398c) with (0x1398c : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (PMs : POSTM C A s m1 m') by (eapply POSTM_mono; [| exact PM']; lia).
  assert (C1 : rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 8) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C2 : rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 16) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C3 : rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 24) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  pose proof (W_sok_win C A' m' _ (s - 48) 48 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO & SHP)].
  2: pose proof (fuzz_covers v SHP) as (FZC1 & FZC2 & FZC3 & FZC4).
  { (* [comment removed for export] *)
    destruct (fz_B0 al_rom r2 m' s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret SOK' C1 C2 C3 Y2 A0) as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    assert (WPf : W C A' (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md) /\ POSTM C A s m1 (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
    { apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    destruct WPf as [HWf PMf].
    apply (KK fx A' _ vm' r3 Hz HWf LQ V10 ltac:(apply cs_kept_intro; csr; reflexivity) PMf).
    apply (aroom_mono _ _ _ _ _ _ Hrm'); lia. }
  (* [comment removed for export] *)
  pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. pose proof (wf_cmap _ WF) as Rcmv.
  destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
  destruct (blk_range C A' m' _ (Z_to_bv 64 (p_data v)) _ CK HW' Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  assert (OTHER : forall q, live A' q <> live A q -> q = Z_to_bv 64 pix \/ q = Z_to_bv 64 (p_data v) \/ (p_cmap v <> 0%Z /\ (q = Z_to_bv 64 (p_cmap v) \/ q = Z_to_bv 64 (c_arr cv)))).
  { intros q NE. destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|N1]; [left; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 (p_data v))) as [->|N2]; [right; left; reflexivity|].
    destruct (Z.eq_dec (p_cmap v) 0) as [Z0|NZ].
    - exfalso. apply NE. apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)].
    - destruct (bv_eq_dec _ q (Z_to_bv 64 (p_cmap v))) as [->|N3]; [right; right; split; [exact NZ | left; reflexivity]|].
      destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [right; right; split; [exact NZ | right; reflexivity]|].
      exfalso. apply NE. apply RQ; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]]. }
  assert (NEWNONE : forall q, live A' q <> live A q -> live A q = None).
  { intros q NE. destruct (OTHER q NE) as [-> | [-> | [NZ [-> | ->]]]]; [exact LpA | exact LdA | |];
      destruct RC as [Z0|(_ & _ & _ & _ & _ & LcA & LaA & _)]; [lia | exact LcA | lia | exact LaA]. }
  destruct (fz_B1 al_rom r2 m' s pix ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
  set (Ma := wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))).
  assert (WPa : W C A' Ma (with_vmmaps vm' md) /\ POSTM C A s m1 Ma).
  { subst Ma. apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
  destruct WPa as [HWa PMa].
  assert (OUTa : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> Ma x = m' x).
  { intros x Hx. subst Ma. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXa : PIXat Ma pix v) by (apply (PIXat_frame m' Ma _ _ PX); intros x Hx; apply OUTa; lia).
  assert (V4 : getr r3 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
  apply (kernelCreateFromPix_W fx C A' Ma _ r3 (s - 48) pix v (Z_to_bv 64 0x139a0) S Hz CK HWa V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 V11 V12 PXa SHP Lp Ld
           (kR - RK_deser)%Z (bR - RB_deser)%Z Hrm' ltac:(lia) ltac:(pose proof (FZC4 size); lia)).
  intros fx2 A3 m3 vm3 r4 Hz2 HW3 CS3 PM3 RES2 Hrm3. rewrite ?with_vmmaps_twice in HW3 |- *. clear Hz.
  replace (Z_to_bv 64 0x139a0) with (0x139a0 : word) by (apply bv_eq; reflexivity).
  pose proof PM3 as [F3 L3].
  (* [comment removed for export] *)
  assert (SUB3 : forall q k, live A' q = Some k -> live A3 q = Some k).
  { intros q k Lq. destruct RES2 as [[_ LQ] | (kel & arr & rows & _ & _ & KR)]; [rewrite LQ; exact Lq|].
    pose proof KR as (_ & _ & _ & K4 & K5 & _ & _ & _ & _ & _ & _ & _ & _ & K14 & K15 & _ & ROWS & _ & RQk).
    rewrite (RQk q); [exact Lq | intros ->; rewrite Lq in K5; discriminate | intros ->; rewrite Lq in K15; discriminate |].
    intros i Hi ->. destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Lq in G7. discriminate. }
  assert (PMa3 : POSTM C A s m1 m3).
  { eapply POSTM_trans; [exact PMa|]. apply (POSTM_sub C A A'); [exact (W_sub0 _ _ _ _ HW') | eapply POSTM_mono; [|exact PM3]; rewrite ?Etop; lia]. }
  assert (Rpp3 : rdn SEGS m3 (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
  { rewrite (FRM_rdn16 C (s - 48) Ma m3 (s - 32) 8 CK F3) by (rewrite ?Etop, ?LV; lia). subst Ma. rewrite <- w2l_Z8 by lia. rdn_solve. }
  assert (D1 : rdn SEGS m3 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 48) Ma m3 (s - 8) 8 CK F3) by (rewrite ?Etop, ?LV; lia). rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
  assert (D2 : rdn SEGS m3 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 48) Ma m3 (s - 16) 8 CK F3) by (rewrite ?Etop, ?LV; lia). rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
  assert (D3 : rdn SEGS m3 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 48) Ma m3 (s - 24) 8 CK F3) by (rewrite ?Etop, ?LV; lia). rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
  assert (PX3 : PIXat m3 pix v).
  { apply (PIXat_frame Ma m3 _ _ PXa). intros x Hx. exact (LIVK_at A' Ma m3 pix 64 x L3 Lp ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) 48 CK HW3 ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK3.
  destruct (fz_C (fx := fx2) al_rom r4 m3 s (getr r4 10) ltac:(lia) ltac:(lia) SOK3 ltac:(csr; reflexivity) eq_refl) as (r5 & RUN5 & X2 & X1 & X10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
  set (Mc := wbytes m3 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr r4 10))).
  assert (WPc : W C A3 Mc (with_vmmaps vm3 md) /\ POSTM C A s m1 Mc).
  { subst Mc. apply (WP_win C A3 A m1 m3 _ _ _ s CK (conj HW3 PMa3)); [| rewrite u_Z2bv by lia; rewrite Etop, LV; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite Etop; lia].
    intros q k Lq. apply SUB3. exact (W_sub0 _ _ _ _ HW' q k Lq). }
  destruct WPc as [HWc PMc].
  assert (OUTc : forall x : word, ~ (s - 40 <= u x < s - 32)%Z -> Mc x = m3 x).
  { intros x Hx. subst Mc. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXc : PIXat Mc pix v) by (apply (PIXat_frame m3 Mc _ _ PX3); intros x Hx; apply OUTc; lia).
  assert (Rppc : rdn SEGS Mc (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
  { rewrite <- Rpp3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTc. lia. }
  assert (X4 : getr r5 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
  apply (pixDestroy_W (fx := fx2) C A3 Mc _ r5 (s - 48) (s - 32) pix (p_cmap v) (4 * c_nalloc cv) (4 * (p_wpl v * p_h v)) v cv (Z_to_bv 64 0x139ac) S
           CK HWc X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
           X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 Rppc PXc Rrc Rtx eq_refl (SUB3 _ _ Lp) Lp0).
  - right. split; [exact (SUB3 _ _ Ld) | split; [exact Ld0 | split; [lia | split; [exact NEdp |]]]].
    intros NZ. destruct RC as [Z0|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NEdc & NEda)]; [lia|]. split; [exact NEdc | exact NEda].
  - destruct RC as [Z0|(NZ & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [left; exact Z0 | right].
    pose proof CM as (Hc0 & Hc64 & _).
    assert (NEpc : Z_to_bv 64 pix <> Z_to_bv 64 (p_cmap v)) by (apply zbv_ne; lia).
    pose proof (live_apart C A' m' _ _ _ _ _ CK HW' Lp Lc NEpc ltac:(lia) ltac:(lia)) as APc. rewrite !u_Z2bv in APc by lia.
    destruct (blk_range C A' m' _ (Z_to_bv 64 (p_cmap v)) 24 CK HW' Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
    split; [| split; [exact (SUB3 _ _ Lc) | split; [exact (SUB3 _ _ La) | split; [exact Lc0 | split; [exact La0 | split; [exact NEca | split; [exact NEcp | split; [exact NEap | exact Hna]]]]]]]].
    apply (CMAPat_frame m' Mc _ _ CM). intros x Hx. rewrite OUTc by lia.
    rewrite (LIVK_at A' Ma m3 (p_cmap v) 24 x L3 Lc ltac:(lia) ltac:(lia) Hx). apply OUTa. lia.
  - intros A5 m5 vm5 r6 HW5 CS5 PD5 PM5 WK5 PMA5 R05 HRT5. rewrite ?with_vmmaps_twice in HW5 |- *.
    pose proof (HRT5 _ _ Hrm3 (proj1 (aroom_nonneg _ _ _ _ Hrm3)) (proj2 (aroom_nonneg _ _ _ _ Hrm3))) as Hrm5. rewrite !Z.sub_0_r in Hrm5.
    replace (Z_to_bv 64 0x139ac) with (0x139ac : word) by (apply bv_eq; reflexivity).
    cbn [p_data] in PD5. destruct PD5 as (E1 & E2 & E3 & E4).
    assert (PM5' : POSTM C A s m1 m5).
    { eapply POSTM_trans; [exact PMc|]. cbn [c_A0] in PM5. eapply POSTM_mono; [|exact PM5]. lia. }
    unfold WKEEP in WK5. rewrite Etop in WK5.
    assert (G1 : rdn SEGS m5 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite <- D1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. rewrite WK5 by lia. apply OUTc. lia. }
    assert (G2 : rdn SEGS m5 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite <- D2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. rewrite WK5 by lia. apply OUTc. lia. }
    assert (G3 : rdn SEGS m5 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite <- D3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. rewrite WK5 by lia. apply OUTc. lia. }
    assert (Gk : rdn SEGS m5 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr r4 10))).
    { transitivity (rdn SEGS Mc (Z_to_bv 64 (s - 40)) 8); [| subst Mc; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia].
      apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply WK5; lia. }
    (* [comment removed for export] *)
    assert (LQ5 : forall q, live A5 q = live A3 q \/ (live A5 q = None /\ live A q = None /\ live A' q <> None)).
    { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|N1]; [right; split; [exact E1 | split; [exact LpA | rewrite Lp; discriminate]]|].
      destruct (bv_eq_dec _ q (Z_to_bv 64 (p_data v))) as [->|N2]; [right; split; [exact (E2 ltac:(lia)) | split; [exact LdA | rewrite Ld; discriminate]]|].
      destruct (Z.eq_dec (p_cmap v) 0) as [Z0|NZ].
      - left. apply E4; [exact N1 | intros _; exact N2 | intros X; exfalso; exact (X Z0)].
      - destruct RC as [Z0|(_ & _ & Lc & La & _ & LcA & LaA & _)]; [lia|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 (p_cmap v))) as [->|N3]; [right; split; [exact (proj1 (E3 NZ)) | split; [exact LcA | rewrite Lc; discriminate]]|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [right; split; [exact (proj2 (E3 NZ)) | split; [exact LaA | rewrite La; discriminate]]|].
        left. apply E4; [exact N1 | intros _; exact N2 | intros _; split; [exact N3 | exact N4]]. }
    assert (GONE5 : forall q k, live A' q = Some k -> live A q = None -> live A5 q = None).
    { intros q k Lq LqA. assert (NE : live A' q <> live A q) by (rewrite Lq, LqA; discriminate).
      destruct (OTHER q NE) as [-> | [-> | [NZ [-> | ->]]]]; [exact E1 | exact (E2 ltac:(lia)) | exact (proj1 (E3 NZ)) | exact (proj2 (E3 NZ))]. }
    assert (FIN3 : forall q, live A3 q = live A' q -> live A5 q = live A q).
    { intros q E3q. destruct (LQ5 q) as [E | (E & EA & _)]; [| rewrite E, EA; reflexivity]. rewrite E, E3q.
      destruct (live A' q) as [k|] eqn:Lq.
      - destruct (live A q) as [k'|] eqn:LqA.
        + destruct (Z.eq_dec k k') as [->|NE]; [reflexivity|]. exfalso. pose proof (NEWNONE q ltac:(rewrite Lq, LqA; congruence)) as X. rewrite LqA in X. discriminate.
        + exfalso. pose proof (GONE5 q k Lq LqA) as G. rewrite E, E3q in G. rewrite ?Lq in G. discriminate.
      - destruct (live A q) as [k'|] eqn:LqA; [| reflexivity]. exfalso. pose proof (NEWNONE q ltac:(rewrite Lq, LqA; discriminate)) as X. rewrite LqA in X. discriminate. }
    destruct (fz_D (fx := fx2) al_rom r6 m5 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r7 & RUN7 & Z2 & Z1 & Z10 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
    assert (Z4 : getr r7 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
    destruct RES2 as [[A40 LQ3] | (kel & arr & rows & A4k & Hk1 & KR)].
    + (* [comment removed for export] *)
      rewrite A40 in Gk.
      apply (kernelDestroy_null_W (fx := fx2) C A5 m5 _ r7 (s - 48) (s - 40) (Z_to_bv 64 0x139b4) S CK HW5 Z2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
               ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia) Z1 ltac:(red; apply bv_eq; reflexivity) Z10 Gk).
      intros m8 r8 HW8 CS8 PM8 R8. replace (Z_to_bv 64 0x139b4) with (0x139b4 : word) by (apply bv_eq; reflexivity).
      pose proof PM8 as [F8 L8]. cbn [c_A0] in L8.
      assert (J1 : rdn SEGS m8 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (rewrite (FRM_rdn16 C (s - 48) m5 m8 (s - 8) 8 CK F8) by (rewrite ?Etop, ?LV; lia); exact G1).
      assert (J2 : rdn SEGS m8 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite (FRM_rdn16 C (s - 48) m5 m8 (s - 16) 8 CK F8) by (rewrite ?Etop, ?LV; lia); exact G2).
      assert (J3 : rdn SEGS m8 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite (FRM_rdn16 C (s - 48) m5 m8 (s - 24) 8 CK F8) by (rewrite ?Etop, ?LV; lia); exact G3).
      destruct (fz_E (fx := fx2) al_rom r8 m8 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret J1 J2 J3 ltac:(csr; reflexivity)) as (r9 & RUN9 & U2 & U1 & U10 & U8 & U9 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN9 |].
      apply (KK fx2 A5 m8 vm5 r9 Hz2 HW8).
      * intros q. apply FIN3. apply LQ3.
      * exact U10.
      * apply cs_kept_intro; csr; reflexivity.
      * eapply POSTM_trans; [exact PM5'|]. eapply POSTM_mono; [|exact PM8]. lia.
      * apply (aroom_mono _ _ _ _ _ _ Hrm5); pose proof (FZC4 size); lia.
    + (* [comment removed for export] *)
      rewrite A4k in Gk.
      pose proof KR as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & ROWS & DIST & RQk).
      pose proof SHP as (Hw1 & Hh1 & (DV & Hw2 & Hh2 & Hsz2) & Ewpl). pose proof (wf_w _ WF). pose proof (wf_h _ WF).
      (* [comment removed for export] *)
      assert (KEEP5 : forall q k, live A3 q = Some k -> live A' q = None -> live A5 q = Some k).
      { intros q k Lq LqN. destruct (LQ5 q) as [E | (E & EA & NN)]; [rewrite E; exact Lq|]. exfalso. exact (NN LqN). }
      pose proof (KEEP5 _ _ K4 K5) as Lk5. pose proof (KEEP5 _ _ K14 K15) as La5.
      pose proof PMA5 as [_ L5]. pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
      assert (M53k : forall x : word, (kel <= u x < kel + 24)%Z -> m5 x = m3 x).
      { intros x Hx. rewrite (LIVK_at A5 Mc m5 kel 24 x L5 Lk5 ltac:(lia) ltac:(lia) Hx). apply OUTc. rewrite Evm in *. lia. }
      assert (M53a : forall x : word, (arr <= u x < arr + 8 * p_h v)%Z -> m5 x = m3 x).
      { intros x Hx. rewrite (LIVK_at A5 Mc m5 arr (8 * p_h v) x L5 La5 ltac:(lia) ltac:(lia) Hx). apply OUTc. rewrite Evm in *. lia. }
      assert (KO5 : kobj C A5 m5 kel arr (p_h v) (p_w v) rows).
      { split; [exact K1|]. split; [exact K2|]. split; [exact Lk5|]. split; [exact K6|].
        split; [rewrite <- K7; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply M53k; lia]|].
        split; [rewrite <- K8; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply M53k; lia]|].
        split; [rewrite <- K9; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply M53k; lia]|].
        split; [exact K10|]. split; [exact K11|]. split; [exact K13|]. split; [exact La5|]. split; [exact K16|]. split; [|exact DIST].
        intros i Hi. destruct (ROWS i Hi) as (Q1' & Q2' & Q3' & Q4' & Q5' & Q6' & Q7' & Q8' & Q9').
        split; [exact Q1'|]. split; [exact Q2'|]. split; [exact Q4'|]. split; [exact Q5'|]. split; [exact (KEEP5 _ _ Q6' Q7')|]. split; [exact Q8'|].
        rewrite <- Q9'. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply M53a. lia. }
      apply (kernelDestroy_W (fx := fx2) C A5 m5 _ r7 (s - 48) (s - 40) kel arr (p_h v) (p_w v) rows (Z_to_bv 64 0x139b4) S CK HW5 Z2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
               Z1 ltac:(red; apply bv_eq; reflexivity) Z4 Z10 Gk KO5 ltac:(lia) ltac:(lia) _ _ Hrm5).
      intros A6 m6 vm6 r8 HW6 CS6 Lk6 La6 LR6 RQ6 PM6 R06 Hrm6. rewrite ?with_vmmaps_twice in HW6 |- *.
      replace (Z_to_bv 64 0x139b4) with (0x139b4 : word) by (apply bv_eq; reflexivity).
      pose proof PM6 as [F6 L6]. cbn [c_A0] in L6.
      assert (J1 : rdn SEGS m6 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (rewrite (FRM_rdn16 C (s - 40 + 8) m5 m6 (s - 8) 8 CK F6) by (rewrite ?Etop, ?LV; lia); exact G1).
      assert (J2 : rdn SEGS m6 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite (FRM_rdn16 C (s - 40 + 8) m5 m6 (s - 16) 8 CK F6) by (rewrite ?Etop, ?LV; lia); exact G2).
      assert (J3 : rdn SEGS m6 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite (FRM_rdn16 C (s - 40 + 8) m5 m6 (s - 24) 8 CK F6) by (rewrite ?Etop, ?LV; lia); exact G3).
      destruct (fz_E (fx := fx2) al_rom r8 m6 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret J1 J2 J3 ltac:(csr; reflexivity)) as (r9 & RUN9 & U2 & U1 & U10 & U8 & U9 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN9 |].
      apply (KK fx2 A6 m6 vm6 r9 Hz2 HW6).
      * intros q.
        assert (NEWK : live A' q = None -> (exists k, live A3 q = Some k) -> live A6 q = None -> live A6 q = live A q).
        { intros LqN _ ->. destruct (live A q) as [k'|] eqn:LqA; [| reflexivity]. exfalso. rewrite (W_sub0 _ _ _ _ HW' q k' LqA) in LqN. discriminate. }
        destruct (bv_eq_dec _ q (Z_to_bv 64 kel)) as [->|N1]; [apply NEWK; [exact K5 | exists 24%Z; exact K4 | exact Lk6]|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|N2]; [apply NEWK; [exact K15 | eexists; exact K14 | exact La6]|].
        destruct (ex_range_dec (fun i => q = Z_to_bv 64 (rows i)) (fun i => bv_eq_dec _ q (Z_to_bv 64 (rows i))) (Z.to_nat (p_h v)) 0) as [(i & Hi & Ei)|NR].
        -- rewrite Z2Nat.id in Hi by lia. destruct (ROWS i ltac:(lia)) as (_ & _ & _ & _ & _ & Q6' & Q7' & _). subst q.
           apply NEWK; [exact Q7' | eexists; exact Q6' | exact (LR6 i ltac:(lia))].
        -- rewrite Z2Nat.id in NR by lia.
           rewrite (RQ6 q N1 N2 ltac:(intros i Hi; apply NR; lia)). apply FIN3. apply (RQk q N1 N2). intros i Hi. apply NR. lia.
      * exact U10.
      * apply cs_kept_intro; csr; reflexivity.
      * eapply POSTM_trans; [exact PM5'|]. eapply POSTM_mono; [|exact PM6]. lia.
      * apply (aroom_mono _ _ _ _ _ _ Hrm6); pose proof (FZC4 size); lia.
Qed.
End Final.
End O17LeptFuzz.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17Kit.
Module O17LeptPinsI.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import O17Kit.
Import O17Drv1.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17LeptBase.
Import O17LeptFuzz.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptCredit.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import O17Kit.O17MallocLayout.

Import O17Drv1.O17FuzzIface.


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

#[export] Instance s17_lept_pins : @LeptPins (@mallocng_alloc_layout LS17) LL17.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LL17 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LS17]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS17] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x507ab 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x507d8 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LS17] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS17] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS17] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LS17] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS17] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS17] in H. lia.
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

#[export] Instance s17_pins16 : @O17Pins (@mallocng_alloc_layout LS17) (@mallocng_calloc_layout LS17).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s17_fuzz_call : forall ACR : @AllocCredit (@mallocng_alloc_layout LS17) (@mallocng_calloc_layout LS17),
  @fuzz_call_contract (@mallocng_alloc_layout LS17) (@mallocng_calloc_layout LS17) (@acr_sure _ _ ACR).
Proof. intros ACR. exact (@lept_fuzz_call _ _ ACR s17_lept_pins s17_pins16). Qed.
End O17LeptPinsI.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require O17Main.
Module O17Pins.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import O17Kit.
Import O17Drv1.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import O17Kit.O17MallocLayout. Import O17Kit.O17Startup. Import O17Kit.O17StartupDefs. Import O17Kit.O17StartupFacts.

Import O17Drv1.O17MainEntry. Import O17Drv1.O17Open. Import O17Drv1.O17Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x507ab) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s17_pins : @O17Main.pins (@mallocng_alloc_layout LS17).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS17] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS17] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS17] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS17] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS17] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x30450 <= a)%Z -> (a + Z.of_nat n <= 0x50818)%Z -> (a + Z.of_nat n <= 0x3047c \/ 0x30480 <= a)%Z ->
              (a + Z.of_nat n <= 0x50560 \/ 0x50780 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS17].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x507ab) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x507ab%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x507ab%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x507ab) + Z.of_nat 0)%Z with 0x507ab%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x507d8%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS17]. change (bv_unsigned (Z_to_bv 64 0x507a8) + 8)%Z with 0x507b0%Z.
        rewrite (LIBC 0x507b0%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x1f180)) with 0x1f180%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End O17Pins.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Spec.
Module O17Closed.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.Spec.
Import O17Kit.
Import O17Pins.
Import O17Drv1.
Import O17LeptPinsI.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17.O17Main.
(* [comment removed for export] *)







Import O17Kit.O17MallocLayout. Import O17Kit.O17Alloc. Import O17Kit.O17Sure. Import O17Kit.O17Credit.


Import O17Drv1.O17FuzzIface.

Import ListNotations.

Theorem s17_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Plain.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@O17Main.ref_realizes_spec_pins _ _ (acr_sure (AllocCredit:=s17_credit)) O17Pins.s17_pins (s17_fuzz_call s17_credit)).
Qed.
End O17Closed.
