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
From OSSVerify.leptonica.colorfill_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8Drv1.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptStderr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL7a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL8a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL9a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptCmapValid.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL11a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptBoxa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptPtra.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptPixa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptCfDestroy.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptCfCreate.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8_code_13734_14000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8_code_15000_16000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8_code_16000_17000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRoomCF.
Module V8LeptFuzz.
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
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptSlots.
Import V8Drv1.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptStderr.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import V8CL7a.
Import V8CL8a.
Import V8CL9a.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptCmapValid.
Import V8CL11a.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBoxa.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptPtra.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptPixa.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptCfDestroy.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptCfCreate.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8_code_13734_14000.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8_code_15000_16000.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8_code_16000_17000.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoomCF.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V8Drv1.V8FuzzIface.


Import V8CL7a.V8LeptErr. Import V8CL7a.V8LeptPixMisc.

Import V8CL8a.V8LeptCmap. Import V8CL8a.V8LeptPixHdr.

Import V8CL9a.V8LeptPixDestroy.


Import V8CL11a.V8LeptDeser. Import V8CL11a.V8LeptCf.


Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sp_slot_al8 : forall sp k : Z, (sp mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((sp - k) mod 8 = 0)%Z.
Proof. intros sp k H1 H2. lia. Qed.
Lemma al16_mod4 : forall p : Z, (p mod 16 = 0)%Z -> (p mod 4 = 0)%Z.
Proof. intros p H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Definition FR3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13da8 : word) m rom) (mkst regs' ret (FR3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13ca4 D_13ca4 (Z_to_bv 64 (s - 48)).
      stepST F_13ca8 D_13ca8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13cac D_13cac (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13cb0 D_13cb0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13cb4 D_13cb4. sn F_13cb8 D_13cb8. stepb_tk F_13cbc D_13cbc ltac:(condZ).
      sn F_13d04 D_13d04.
      stepLD8 F_13d08 D_13d08 ret. stepLD8 F_13d0c D_13d0c (getr regs 8). stepLD8 F_13d10 D_13d10 (getr regs 9).
      zv F_13d14 D_13d14 (Z_to_bv 64 s). stepret F_13d18 D_13d18 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_big : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0x21818) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13da8 : word) m rom)
                              (mkst regs' (0x16898 : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0x21818) (word_to_le_bytes 8 (Z_to_bv 64 0x13e20))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13de0 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_13ca4 D_13ca4 (Z_to_bv 64 (s - 48)).
      stepST F_13ca8 D_13ca8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13cac D_13cac (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13cb0 D_13cb0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13cb4 D_13cb4. sn F_13cb8 D_13cb8. stepb_ft F_13cbc D_13cbc ltac:(condZ).
      sn F_13cc0 D_13cc0. sn F_13cc4 D_13cc4. sn F_13cc8 D_13cc8. sn F_13ccc D_13ccc.
      stepb_tk F_13e3c D_13e3c ltac:(condZ).
      sn F_13e48 D_13e48.
      stepST F_13e4c D_13e4c (Z_to_bv 64 0x21818) (Z_to_bv 64 0x13e20) ltac:(store_ok_peel; exact SOKh).
      stepret F_13e50 D_13e50 (0x13dd4 : word) ltac:(bveq).
      sn F_13cd0 D_13cd0. sn F_13cd4 D_13cd4. sn F_13cd8 D_13cd8. sn F_16790 D_16790. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13e08 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_13d04 D_13d04.
      stepLD8 F_13d08 D_13d08 ret. stepLD8 F_13d0c D_13d0c s0v. stepLD8 F_13d10 D_13d10 s1v.
      zv F_13d14 D_13d14 (Z_to_bv 64 s). stepret F_13d18 D_13d18 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x13de0 : word) m rom) (mkst regs' (0x13e08 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r ([] : list (bv 5))) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_13cdc D_13cdc (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_13ce0 D_13ce0 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. all: solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x13de0 : word) m rom)
       (mkst regs' (0x16d84 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 1 = Z_to_bv 64 0x13df4
      /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Hp SOK H2 H10. eexists. split.
    - stepST F_13cdc D_13cdc (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_13ce0 D_13ce0 ltac:(condZ).
      sn F_13ce4 D_13ce4. sn F_13ce8 D_13ce8. sn F_13cec D_13cec. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s cf : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= cf < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 cf ->
    exists regs', msteps SEGS (mkst regs (0x13df4 : word) m rom)
       (mkst regs' (0x17030 : word) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 cf))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 (s - 40) /\ getr regs' 1 = Z_to_bv 64 0x13e00
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s cf Hs Hs64 Hcf SOK H2 H10. eexists. split.
    - stepST F_13cf0 D_13cf0 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 cf) ltac:(sok_in SOK).
      zv F_13cf4 D_13cf4 (Z_to_bv 64 (s - 40)). sn F_13cf8 D_13cf8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_D : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13e00 : word) m rom) (mkst regs' (0x154fc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x13e08
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_13cfc D_13cfc (Z_to_bv 64 (s - 32)). sn F_13d00 D_13d00. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma keeps_below : forall C A m m' md md' (q : Z), Cok C -> W C A m md -> W C A m' md' ->
  (forall x : word, (u x < c_top C - LSTK)%Z -> m' x = m x) -> (0 <= q < 2 ^ 64)%Z -> keeps A A m m' q.
Proof.
  intros C A m m' md md' q CK HW HW' OUT Hq. apply (keeps_agree C A A m m' md' q HW' eq_refl Hq).
  intros k x L Hx. apply OUT.
  destruct (blk_range C A m md (Z_to_bv 64 q) k CK HW L ltac:(destruct (Z_lt_le_dec 0 k); [exact l | exfalso; clear -Hx l; lia])) as [_ TOP].
  rewrite u_Z2bv in TOP by lia. pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val. clear -Hx TOP T1 H. lia.
Qed.

(* [comment removed for export] *)
Lemma live_ne0 : forall C A m md (q : word) n, Cok C -> W C A m md -> live A q = Some n -> (0 < n)%Z -> Z_to_bv 64 0 <> q.
Proof.
  intros C A m md q n CK HW L Hn E. subst q. destruct (blk_range C A m md (Z_to_bv 64 0) n CK HW L Hn) as [G _].
  rewrite u_Z2bv in G by lia. lia.
Qed.

Lemma set_rc_eta : forall v a b, p_rc v = b -> set_rc (set_rc v a) b = v.
Proof. intros v a b <-. destruct v; reflexivity. Qed.

(* [comment removed for export] *)
Lemma POSTD_POSTM_sub_win : forall C A A' m' md' (s s' pp : Z) m, Cok C -> W C A' m' md' -> sub_live A A' ->
  (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s')%Z -> (s <= s')%Z -> (s' <= c_top C)%Z -> POSTD C A s pp m m' -> POSTM C A s' m m'.
Proof.
  intros C A A' m' md' s s' pp m CK HW SUB Hlo Hhi Hs Hs' [F L]. split.
  - intros a H1 H2 H3 H4 H5. apply F; try assumption; unfold scratch, inslot in *; lia.
  - intros q k i Lq Hi. apply (L q k i Lq Hi). intros IN. unfold inslot in IN.
    pose proof (SUB q k Lq) as Lq'.
    pose proof (ai_live_hull A' m' (m_vmmaps md') q k (w_inv _ _ _ _ HW) Lq') as (Hk0 & _ & TOP & _). pose proof (round16_ge k Hk0).
    pose proof (alloc_top_lt (m_vmmaps md')) as T. unfold two_pow_64 in T.
    assert (R : (u q <= u (at_ q i) < u q + k)%Z) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia).
    destruct (blk_byte C A' m' md' q k (at_ q i) CK HW Lq' R) as (_ & _ & _ & NW & _). apply NW. unfold win.
    pose proof (ck_top C CK). lia.
Qed.

(* [comment removed for export] *)
Lemma cf_ok_transport : forall C A0 A m m' v o,
  cf_ok C A0 A m v o -> (forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A A m m' q) -> cf_ok C A0 A m' v o.
Proof.
  intros C A0 A m m' v o CF KP.
  pose proof CF as (RC & Lcf & L0cf & PX & RC2 & Halp & Lpix & L0pix & OBA & ONAA & ODNAA & OPX & REST).
  pose proof (RECat_range m _ _ RC) as [Hcf0 Hcf1]. cbn in Hcf1.
  pose proof PX as (Hp0 & Hp64 & _ & _).
  destruct (KP (o_cf o) ltac:(lia) _ Lcf) as (_ & _ & Mcf). destruct (KP (o_pix o) ltac:(lia) _ Lpix) as (_ & _ & Mpix).
  split; [apply (RECat_frame m m' _ _ RC); intros x Hx; apply Mcf; cbn in Hx; lia|].
  split; [exact Lcf|]. split; [exact L0cf|].
  split; [apply (PIXat_frame m m' _ v PX); intros x Hx; apply Mpix; lia|].
  split; [exact RC2|]. split; [exact Halp|]. split; [exact Lpix|]. split; [exact L0pix|].
  split.
  { destruct OBA as [Z0 | (BA & NE & NB)]; [left; exact Z0 | right]. split; [| split; [exact NE | exact NB]].
    pose proof BA as (RB & _ & _ & _ & ARR). pose proof (RECat_range m _ _ RB) as [B0 B1]. cbn in B1.
    pose proof (BOXA_wf m _ _ _ _ _ RB) as (_ & _ & Warr & _).
    apply (boxa_at_transport C A A m m' _ _ _ _ _ BA (KP (o_ba o) ltac:(lia)) (KP (o_barr o) ltac:(lia))).
    intros Hn1. destruct ARR as [[_ Hn0] | (_ & _ & _ & _ & NBX)]; [lia|].
    destruct NBX as [Hn0 | (_ & _ & BX1 & _ & _)]; [lia|]. destruct BX1 as ((x & y & w & h & RBX) & _).
    pose proof (RECat_range m _ _ RBX) as [X0 X1]. cbn in X1. apply KP. lia. }
  split.
  { destruct ONAA as [Z0 | (PA & NE)]; [left; exact Z0 | right]. split; [| exact NE].
    pose proof PA as (RP & _). pose proof (RECat_range m _ _ RP) as [P0 P1]. cbn in P1.
    pose proof (PTRA_wf m _ _ _ _ RP) as (_ & _ & Warr & _).
    exact (ptra_at_transport C A A m m' _ _ _ PA (KP (o_naa o) ltac:(lia)) (KP (o_narr o) ltac:(lia))). }
  split.
  { destruct ODNAA as [Z0 | (PA & NE)]; [left; exact Z0 | right]. split; [| exact NE].
    pose proof PA as (RP & _). pose proof (RECat_range m _ _ RP) as [P0 P1]. cbn in P1.
    pose proof (PTRA_wf m _ _ _ _ RP) as (_ & _ & Warr & _).
    exact (ptra_at_transport C A A m m' _ _ _ PA (KP (o_dnaa o) ltac:(lia)) (KP (o_darr o) ltac:(lia))). }
  split.
  { destruct OPX as [Z0 | PXA]; [left; exact Z0 | right].
    pose proof PXA as (RP & _ & _ & _ & _ & _ & _ & _ & BA & _). pose proof (RECat_range m _ _ RP) as [P0 P1]. cbn in P1.
    pose proof (PIXA_wf m _ _ _ _ _ _ RP) as (_ & _ & Wparr & Wba & _).
    pose proof BA as (RB & _). pose proof (BOXA_wf m _ _ _ _ _ RB) as (_ & _ & Wbarr & _).
    exact (pixa_at_transport C A A m m' _ _ _ _ _ _ PXA (KP (o_px o) ltac:(lia)) (KP (o_parr o) ltac:(lia)) (KP (o_pba o) ltac:(lia)) (KP (o_pbarr o) ltac:(lia))). }
  exact REST.
Qed.
End FuzzSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_colorfill <= FUZZ_CALLS)%Z /\ (forall size, (0 <= size)%Z -> (RB_colorfill <= fuzz_margin size)%Z).
Proof. rewrite RK_colorfill_val. pose proof RB_colorfill_le. unfold FUZZ_CALLS, fuzz_margin. split; [lia | intros; lia]. Qed.

Theorem lept_fuzz_call : @fuzz_call_contract AL CL ASR.
Proof.
  unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hz0 Hpl Hempty Hal16 Hra Hret Hgp Htp Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm. pose proof (FZb size ltac:(lia)) as FZb'.
  assert (RKd : (0 <= RK_deser)%Z /\ (0 <= RB_deser)%Z /\ (0 <= RK_cf)%Z /\ (0 <= RB_cf)%Z /\ RK_colorfill = (RK_deser + RK_cf)%Z /\ RB_colorfill = (RB_deser + RB_cf)%Z)
    by (room_consts; repeat split; lia).
  destruct RKd as (RKd0 & RBd0 & RKc0 & RBc0 & RKe & RBe).
  rewrite pu8_segs in Hhdl, K |- *. rewrite pu8_tp in Htp.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x13da8) with (0x13da8 : word) by (apply bv_eq; reflexivity).
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
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
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
    rewrite <- (with_vmmaps_same md). apply (K A (FR3 m s ret regs) (m_vmmaps md) r1).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 48)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q k L; exact L.
    - exact Hz0.
    - exact Q10.
    - apply cs_kept_intro; csr; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - apply (aroom_mono A (m_vmmaps md) kR bR); [exact Hrm | lia | lia]. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x21818) 8 = true) by exact Hhdl.
  destruct (fz_big al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FR3 m s ret regs) (Z_to_bv 64 0x21818) (word_to_le_bytes 8 (Z_to_bv 64 0x13e20))) in *.
  assert (OUT1 : forall a : word, ~ (s - 48 <= u a < s)%Z -> ~ (0x21818 <= u a < 0x21818 + 8)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LLU8] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 48)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x21818); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) (0x21818 + 8)); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite pu8_segs. subst m1. cbn [ll_hcell ll_devnull LLU8]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  assert (CE1 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
                rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
                rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { subst m1. unfold FR3. repeat split; rdn_solve. }
  (* [comment removed for export] *)
  assert (KK : forall A' mf vm' rr, W C A' mf (with_vmmaps vm' md) -> live A' (Z_to_bv 64 0) = None -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> POSTM C A s m1 mf -> aroom A' vm' (kR - FUZZ_CALLS) (bR - fuzz_margin size) -> realizes SEGS (mkCfg (mkst rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros A' mf vm' rr HWf Z0f A0 CS [F L] HRf. apply (K A' mf vm' rr).
    - pose proof (w_inv _ _ _ _ HWf) as X. rewrite with_vmmaps_vmmaps in X. exact X.
    - exact (W_sub0 _ _ _ _ HWf).
    - exact Z0f.
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
  (* [comment removed for export] *)
  assert (TAIL : forall A' M vm' rr, W C A' M (with_vmmaps vm' md) -> live A' (Z_to_bv 64 0) = None ->
             (forall x, In x cs_rest -> getr rr x = getr regs x) -> getr rr 2 = Z_to_bv 64 (s - 48) ->
             POSTM C A s m1 M ->
             rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
             rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
             rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
             aroom A' vm' (kR - FUZZ_CALLS) (bR - fuzz_margin size) ->
             realizes SEGS (mkCfg (mkst rr (0x13e08 : word) M al_rom) (with_vmmaps vm' md)) S).
  { intros A' M vm' rr HW' Z0' RR Y PM' D1 D2 D3 RMt.
    destruct (fz_E al_rom rr M s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret D1 D2 D3 Y) as (r9 & RUN9 & U2 & U1 & U10 & U8 & U9 & AG9).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN9 |].
    apply (KK A' M vm' r9 HW' Z0' U10); [| exact PM' | exact RMt].
    apply cs_kept_of_rest; [rewrite U2, H2; reflexivity | exact U8 | exact U9 | rest_solve]. }
  apply (pixDeserialize_W C A m1 md r1 (s - 48) dp pl (Z_to_bv 64 0x13de0) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia) ltac:(apply al16_mod4; exact Hal16)
           kR bR Hrm ltac:(lia) ltac:(lia)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x13de0) with (0x13de0 : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (PMs : POSTM C A s m1 m') by (eapply POSTM_mono; [| exact PM']; lia).
  pose proof CE1 as (C1 & C2 & C3).
  rewrite <- (FRM_rdn16 C (s - 48) m1 m' (s - 8) 8 CK F') in C1 by (rewrite ?Etop, ?LV; lia).
  rewrite <- (FRM_rdn16 C (s - 48) m1 m' (s - 16) 8 CK F') in C2 by (rewrite ?Etop, ?LV; lia).
  rewrite <- (FRM_rdn16 C (s - 48) m1 m' (s - 24) 8 CK F') in C3 by (rewrite ?Etop, ?LV; lia).
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (RR2 : forall x, In x cs_rest -> getr r2 x = getr regs x) by rest_solve.
  pose proof (W_sok_win C A' m' _ (s - 48) 48 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO)].
  - (* [comment removed for export] *)
    destruct (fz_B0 al_rom r2 m' s ltac:(lia) ltac:(lia) SOK' Y2 A0) as (r3 & RUN3 & V2 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (Mb := wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WPf : W C A' Mb (with_vmmaps vm' md) /\ POSTM C A s m1 Mb).
    { subst Mb. apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    destruct WPf as [HWf PMf].
    assert (OUTb : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> Mb x = m' x).
    { intros x Hx. subst Mb. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    apply (TAIL A' Mb vm' r3 HWf); [rewrite LQ; exact Hz0 | rest_solve | exact V2 | exact PMf | | | |].
    + rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia.
    + rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia.
    + rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTb; lia.
    + apply (aroom_mono A' vm' (kR - RK_deser) (bR - RB_deser)); [exact Hrm' | lia | lia].
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
    destruct (blk_range C A' m' _ (Z_to_bv 64 (p_data v)) _ CK HW' Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    pose proof (ai_live_hull A' m' _ _ _ (w_inv _ _ _ _ HW') Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
    assert (Z0' : live A' (Z_to_bv 64 0) = None).
    { rewrite (RQ (Z_to_bv 64 0)); [exact Hz0 | apply zbv_ne; lia | apply zbv_ne; lia |].
      intros NZ. destruct RC as [Z0|(Hc1 & CM & Lc & La & Hna & _)]; [lia|].
      split; [exact (live_ne0 C A' m' _ _ _ CK HW' Lc ltac:(lia)) | exact (live_ne0 C A' m' _ _ _ CK HW' La Hna)]. }
    destruct (fz_B1 al_rom r2 m' s pix ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V2 & V10 & V11 & V12 & V1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (Ma := wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    assert (WPa : W C A' Ma (with_vmmaps vm' md) /\ POSTM C A s m1 Ma).
    { subst Ma. apply (WP_win C A' A m1 m' _ _ _ s CK (conj HW' PMs) (W_sub0 _ _ _ _ HW')); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    destruct WPa as [HWa PMa].
    assert (OUTa : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> Ma x = m' x).
    { intros x Hx. subst Ma. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (Ka : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A' A' m' Ma q).
    { intros q Hq. apply (keeps_below C A' m' Ma _ _ q CK HW' HWa); [| exact Hq]. intros x Hx. apply OUTa. rewrite Etop, LV in Hx. lia. }
    assert (Rpix : rdn SEGS Ma (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
    { subst Ma. rewrite <- w2l_Z8 by lia. rdn_solve. }
    assert (Ca1 : rdn SEGS Ma (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
    assert (Ca2 : rdn SEGS Ma (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
    assert (Ca3 : rdn SEGS Ma (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTa; lia. }
    apply (l_colorfillCreate_main C A' Ma (with_vmmaps vm' md) r3 (s - 48) pix v (Z_to_bv 64 0x13df4) S CK HWa V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia)
             V1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) V10 V11 V12
             ltac:(apply (PIXat_frame m' Ma pix v PX); intros x Hx; apply OUTa; lia) Rrc Lp Lp0 ALp Z0' ltac:(exact Hz0)
             (kR - RK_deser) (bR - RB_deser) ltac:(rewrite with_vmmaps_vmmaps; exact Hrm') ltac:(lia) ltac:(lia)).
    intros A2 m2 vm2 r4 HW2 CS2 PM2 Z02 RES2 Hrm2. rewrite with_vmmaps_twice in HW2 |- *.
    replace (Z_to_bv 64 0x13df4) with (0x13df4 : word) by (apply bv_eq; reflexivity).
    pose proof PM2 as [F2 L2]. cbn [c_A0] in L2.
    assert (PM2s : POSTM C A s m1 m2) by (eapply POSTM_trans; [exact PMa | eapply POSTM_mono; [| exact PM2]; lia]).
    assert (Y4 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (RR4 : forall x, In x cs_rest -> getr r4 x = getr regs x) by rest_solve.
    pose proof (W_sok_win C A2 m2 _ (s - 48) 48 CK HW2 ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK2.
    pose proof Ca1 as D1. pose proof Ca2 as D2. pose proof Ca3 as D3. pose proof Rpix as Dpix.
    rewrite <- (FRM_rdn16 C (s - 48) Ma m2 (s - 8) 8 CK F2) in D1 by (rewrite ?Etop, ?LV; lia).
    rewrite <- (FRM_rdn16 C (s - 48) Ma m2 (s - 16) 8 CK F2) in D2 by (rewrite ?Etop, ?LV; lia).
    rewrite <- (FRM_rdn16 C (s - 48) Ma m2 (s - 24) 8 CK F2) in D3 by (rewrite ?Etop, ?LV; lia).
    rewrite <- (FRM_rdn16 C (s - 48) Ma m2 (s - 32) 8 CK F2) in Dpix by (rewrite ?Etop, ?LV; lia).
    (* [comment removed for export] *)
    assert (CFV : exists cfv : Z, getr r4 10 = Z_to_bv 64 cfv /\ (0 <= cfv < 2 ^ 64)%Z).
    { destruct RES2 as [[A0 _] | (o & A0 & _ & _ & _ & CF & _)]; [exists 0%Z; split; [exact A0 | lia]|].
      pose proof CF as (RC' & _). pose proof (RECat_range m2 _ _ RC') as [X0 X1]. cbn in X1. exists (o_cf o). split; [exact A0 | lia]. }
    destruct CFV as (cfv & A4 & Hcfv).
    destruct (fz_C al_rom r4 m2 s cfv ltac:(lia) ltac:(lia) Hcfv SOK2 Y4 A4) as (r5 & RUN5 & X2 & X10 & X1 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
    set (Mc := wbytes m2 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 cfv))).
    assert (WPc : W C A2 Mc (with_vmmaps vm2 md) /\ POSTM C A s m1 Mc).
    { subst Mc. apply (WP_win C A2 A m1 m2 _ _ _ s CK (conj HW2 PM2s) (W_sub0 _ _ _ _ HW2)); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; rewrite ?Etop, ?LV; cbn; rewrite ?Etop, ?LV; lia. }
    destruct WPc as [HWc PMc].
    assert (OUTc : forall x : word, ~ (s - 40 <= u x < s - 32)%Z -> Mc x = m2 x).
    { intros x Hx. subst Mc. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (Kc : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A2 A2 m2 Mc q).
    { intros q Hq. apply (keeps_below C A2 m2 Mc _ _ q CK HW2 HWc); [| exact Hq]. intros x Hx. apply OUTc. rewrite Etop, LV in Hx. lia. }
    assert (Rcf : rdn SEGS Mc (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 cfv)).
    { subst Mc. rewrite <- w2l_Z8 by lia. rdn_solve. }
    assert (Dc1 : rdn SEGS Mc (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite <- D1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTc; lia. }
    assert (Dc2 : rdn SEGS Mc (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite <- D2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTc; lia. }
    assert (Dc3 : rdn SEGS Mc (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite <- D3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTc; lia. }
    assert (Dcpix : rdn SEGS Mc (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
    { rewrite <- Dpix. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUTc; lia. }
    (* [comment removed for export] *)
    assert (DST : forall A3 M3 vm3 r6, W C A3 M3 (with_vmmaps vm3 md) ->
              (forall x, In x cs_rest -> getr r6 x = getr regs x) -> getr r6 2 = Z_to_bv 64 (s - 48) ->
              live A3 (Z_to_bv 64 0) = None -> POSTM C A s m1 M3 ->
              rdn SEGS M3 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
              rdn SEGS M3 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
              rdn SEGS M3 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
              rdn SEGS M3 (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix) ->
              PIXat M3 pix v ->
              (forall (q : Z) k, live A' (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> pix -> keeps A' A3 m' M3 q) ->
              live A3 (Z_to_bv 64 pix) = Some 64%Z ->
              aroom A3 vm3 (kR - FUZZ_CALLS) (bR - fuzz_margin size) ->
              realizes SEGS (mkCfg (mkst r6 (0x13e00 : word) M3 al_rom) (with_vmmaps vm3 md)) S).
    { intros A3 M3 vm3 r6 HW3 RR6 Y6 Z03 PM3 E1 E2 E3 Epix PX3 K3 Lp3 RM3.
      destruct (fz_D al_rom r6 M3 s ltac:(lia) ltac:(lia) Y6) as (r7 & RUN7 & W2 & W10 & W1 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN7 |].
      assert (KD : p_data v = 0%Z \/ (live A3 (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\
                   (0 < 4 * (p_wpl v * p_h v))%Z /\ p_data v <> pix /\ (p_cmap v <> 0%Z -> p_data v <> p_cmap v /\ p_data v <> c_arr cv))).
      { right. destruct (K3 (p_data v) _ Ld ltac:(lia) NEdp _ Ld) as (Ld3 & _ & _).
        split; [exact Ld3|]. split; [exact Ld0|]. split; [lia|]. split; [exact NEdp|].
        intros NZ. destruct RC as [Z0|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NEdc & NEda)]; [lia|]. split; [exact NEdc | exact NEda]. }
      assert (KC : p_cmap v = 0%Z \/ (CMAPat M3 (p_cmap v) cv /\ live A3 (Z_to_bv 64 (p_cmap v)) = Some 24%Z /\ live A3 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                   live (c_A0 C) (Z_to_bv 64 (p_cmap v)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                   p_cmap v <> c_arr cv /\ p_cmap v <> pix /\ c_arr cv <> pix /\ (0 < 4 * c_nalloc cv)%Z)).
      { destruct RC as [Z0|(NZ & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [left; exact Z0 | right].
        pose proof CM as (Hc0 & Hc64 & WFc & _). pose proof (cf_arr _ WFc) as Har.
        destruct (K3 (p_cmap v) _ Lc ltac:(lia) NEcp _ Lc) as (Lc3 & _ & Mc3).
        destruct (K3 (c_arr cv) _ La Har NEap _ La) as (La3 & _ & _).
        split; [apply (CMAPat_frame m' M3 _ _ CM); intros x Hx; apply Mc3; lia|].
        split; [exact Lc3|]. split; [exact La3|]. split; [exact Lc0|]. split; [exact La0|].
        split; [exact NEca|]. split; [exact NEcp|]. split; [exact NEap | exact Hna]. }
      apply (pixDestroy_W C A3 M3 _ r7 (s - 48) (s - 32) pix (p_cmap v) (4 * c_nalloc cv) (4 * (p_wpl v * p_h v)) v cv (Z_to_bv 64 0x13e08) S
               CK HW3 W2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
               W1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hsp16 | reflexivity]) W10 Epix PX3 Rrc Rtx eq_refl Lp3 Lp0 KD KC).
      intros A5 m5 vm5 r8 HW5 CS5 PD5 PM5 R0 HRT5. rewrite with_vmmaps_twice in HW5 |- *.
      replace (Z_to_bv 64 0x13e08) with (0x13e08 : word) by (apply bv_eq; reflexivity).
      pose proof PM5 as [F5 L5].
      apply (TAIL A5 m5 vm5 r8 HW5).
      + destruct PD5 as (E1' & E2' & E3' & E4'). rewrite (E4' (Z_to_bv 64 0)); [exact Z03 | apply zbv_ne; lia | intros NZ; apply zbv_ne; lia |].
        intros NZ. destruct KC as [Z0|(CM3 & Lc3 & La3 & _ & _ & _ & _ & _ & Hna3)]; [lia|].
        split; [exact (live_ne0 C A3 M3 _ _ _ CK HW3 Lc3 ltac:(lia)) | exact (live_ne0 C A3 M3 _ _ _ CK HW3 La3 Hna3)].
      + rest_solve.
      + csr; reflexivity.
      + eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [| exact PM5]; lia].
      + rewrite (FRM_rdn16 C (s - 32 + 8) M3 m5 (s - 8) 8 CK F5) by (rewrite ?Etop, ?LV; lia). exact E1.
      + rewrite (FRM_rdn16 C (s - 32 + 8) M3 m5 (s - 16) 8 CK F5) by (rewrite ?Etop, ?LV; lia). exact E2.
      + rewrite (FRM_rdn16 C (s - 32 + 8) M3 m5 (s - 24) 8 CK F5) by (rewrite ?Etop, ?LV; lia). exact E3.
      + exact (roomtr_app0_wv A3 vm3 md A5 vm5 _ _ HRT5 RM3 ltac:(lia) ltac:(lia)). }
    destruct RES2 as [[A0 KP2] | (o & A0 & Eop & _ & _ & CF & KP2)].
    + (* [comment removed for export] *)
      rewrite A0 in A4. assert (Ecfv : cfv = 0%Z).
      { apply (f_equal bv_unsigned) in A4. rewrite !u_Z2bv in A4 by lia. lia. }
      subst cfv.
      apply (l_colorfillDestroy_null_W C A2 Mc (with_vmmaps vm2 md) r5 (s - 48) (s - 40) (Z_to_bv 64 0x13e00) S CK HWc X2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; lia)
               X1 ltac:(red; apply bv_eq; reflexivity) X10 ltac:(lia) ltac:(rewrite Etop; lia) ltac:(apply sp_slot_al8; [exact Hsp16 | reflexivity]) Rcf).
      intros M3 r6 HW3 CS3 PM3n. replace (Z_to_bv 64 0x13e00) with (0x13e00 : word) by (apply bv_eq; reflexivity).
      pose proof PM3n as [F3 L3].
      assert (K23 : forall q : Z, (0 <= q < 2 ^ 64)%Z -> keeps A2 A2 Mc M3 q).
      { intros q Hq. exact (keeps_postm C A2 A2 A2 (s - 48) Mc M3 _ q HW3 PM3n eq_refl eq_refl Hq). }
      assert (K3 : forall (q : Z) k, live A' (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> keeps A' A2 m' M3 q).
      { intros q k L Hq. apply (keeps_trans _ _ _ _ _ _ _ (Ka q Hq)). apply (keeps_trans _ _ _ _ _ _ _ (KP2 q k L Hq)).
        apply (keeps_trans _ _ _ _ _ _ _ (Kc q Hq)). exact (K23 q Hq). }
      destruct (K3 pix _ Lp ltac:(lia) _ Lp) as (Lp3 & _ & Mp3).
      apply (DST A2 M3 vm2 r6 HW3 ltac:(rest_solve) ltac:(csr; reflexivity) Z02).
      * eapply POSTM_trans; [exact PMc|]. apply (POSTM_sub C A A2 _ _ _ (W_sub0 _ _ _ _ HW2)). eapply POSTM_mono; [| exact PM3n]. lia.
      * rewrite (FRM_rdn16 C (s - 48) Mc M3 (s - 8) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact Dc1.
      * rewrite (FRM_rdn16 C (s - 48) Mc M3 (s - 16) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact Dc2.
      * rewrite (FRM_rdn16 C (s - 48) Mc M3 (s - 24) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact Dc3.
      * rewrite (FRM_rdn16 C (s - 48) Mc M3 (s - 32) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact Dcpix.
      * apply (PIXat_frame m' M3 pix v PX). intros x Hx. apply Mp3. lia.
      * intros q k L Hq _. exact (K3 q k L Hq).
      * exact Lp3.
      * apply (aroom_mono A2 vm2 (kR - RK_deser - RK_cf) (bR - RB_deser - RB_cf)); [exact Hrm2 | lia | lia].
    + (* [comment removed for export] *)
      rewrite A0 in A4. assert (Ecfv : cfv = o_cf o).
      { pose proof CF as (RC' & _). pose proof (RECat_range m2 _ _ RC') as [Y0 Y1]. cbn in Y1.
        apply (f_equal bv_unsigned) in A4. rewrite !u_Z2bv in A4 by lia. lia. }
      subst cfv. subst pix.
      pose proof (cf_ok_transport C A' A2 m2 Mc _ o CF Kc) as CFc.
      apply (l_colorfillDestroy_main C A' A2 Mc (with_vmmaps vm2 md) r5 (s - 48) (s - 40) (Z_to_bv 64 0x13e00) (set_rc v 2) o S CK
               ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(rewrite Etop; lia)
               ltac:(red; apply bv_eq; reflexivity) X2 ltac:(csr; reflexivity) ltac:(lia) ltac:(rewrite Etop; lia) ltac:(apply sp_slot_al8; [exact Hsp16 | reflexivity]) ltac:(exact Hz0) CFc HWc); [| exact X1 | exact X10 | exact Rcf].
      intros A3 M3 vm3 r6 HW3 CS3 PX3 Lp3 KP3 SUB3 PD3 R03 HRT3. rewrite with_vmmaps_twice in HW3 |- *.
      replace (Z_to_bv 64 0x13e00) with (0x13e00 : word) by (apply bv_eq; reflexivity).
      rewrite (set_rc_eta v 2 1 Rrc) in PX3.
      assert (Z03 : live A3 (Z_to_bv 64 0) = None).
      { destruct (live A3 (Z_to_bv 64 0)) as [k|] eqn:E; [|reflexivity]. pose proof (SUB3 _ _ E). congruence. }
      assert (K3 : forall (q : Z) k, live A' (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> q <> o_pix o -> keeps A' A3 m' M3 q).
      { intros q k L Hq NE. apply (keeps_trans _ _ _ _ _ _ _ (Ka q Hq)). apply (keeps_trans _ _ _ _ _ _ _ (KP2 q k L Hq NE)).
        apply (keeps_trans _ _ _ _ _ _ _ (Kc q Hq)). exact (KP3 q k L Hq NE). }
      pose proof (POSTD_rdn_above C (c_A0 C) (s - 48) (s - 40) Mc M3 (s - 8) 8 CK PD3 ltac:(lia) ltac:(lia) ltac:(rewrite Etop, LV; lia) ltac:(lia)) as G1.
      pose proof (POSTD_rdn_above C (c_A0 C) (s - 48) (s - 40) Mc M3 (s - 16) 8 CK PD3 ltac:(lia) ltac:(lia) ltac:(rewrite Etop, LV; lia) ltac:(lia)) as G2.
      pose proof (POSTD_rdn_above C (c_A0 C) (s - 48) (s - 40) Mc M3 (s - 24) 8 CK PD3 ltac:(lia) ltac:(lia) ltac:(rewrite Etop, LV; lia) ltac:(lia)) as G3.
      pose proof (POSTD_rdn_above C (c_A0 C) (s - 48) (s - 40) Mc M3 (s - 32) 8 CK PD3 ltac:(lia) ltac:(lia) ltac:(rewrite Etop, LV; lia) ltac:(lia)) as G4.
      rewrite pu8_segs in G1, G2, G3, G4.
      apply (DST A3 M3 vm3 r6 HW3 ltac:(rest_solve) ltac:(csr; reflexivity) Z03).
      * eapply POSTM_trans; [exact PMc|].
        apply (POSTD_POSTM_sub_win C A A3 M3 _ (s - 48) s (s - 40) Mc CK HW3 (W_sub0 _ _ _ _ HW3)); [rewrite Etop, LV; lia | lia | lia | rewrite Etop; lia | exact PD3].
      * rewrite G1. exact Dc1.
      * rewrite G2. exact Dc2.
      * rewrite G3. exact Dc3.
      * rewrite G4. exact Dcpix.
      * exact PX3.
      * exact K3.
      * exact Lp3.
      * apply (roomtr_app0_wv A2 vm2 md A3 vm3 _ _ HRT3); [apply (aroom_mono A2 vm2 (kR - RK_deser - RK_cf) (bR - RB_deser - RB_cf)); [exact Hrm2 | lia | lia] | lia | lia].
Qed.
End Final.
End V8LeptFuzz.

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8Kit.
Module V8LeptPinsI.
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
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import V8Kit.
Import V8Drv1.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import V8LeptFuzz.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V8Kit.V8MallocLayout.

Import V8Drv1.V8FuzzIface.



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

#[export] Instance u8_lept_pins : @LeptPins (@mallocng_alloc_layout LU8) LLU8.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LLU8 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LU8]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU8] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x51dfb 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x51e28 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LU8] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU8] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU8] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LU8] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU8] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU8] in H. lia.
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

#[export] Instance u8_pins8 : @V8Pins (@mallocng_alloc_layout LU8) (@mallocng_calloc_layout LU8).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem u8_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LU8) (@mallocng_calloc_layout LU8),
  @fuzz_call_contract (@mallocng_alloc_layout LU8) (@mallocng_calloc_layout LU8) ASR.
Proof. intros ASR. exact (@lept_fuzz_call _ _ ASR u8_lept_pins u8_pins8). Qed.
End V8LeptPinsI.

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8Main.
Module V8Pins.
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
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import V8Kit.
Import V8Drv1.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V8Kit.V8MallocLayout. Import V8Kit.V8Startup. Import V8Kit.V8StartupDefs. Import V8Kit.V8StartupFacts.

Import V8Drv1.V8MainEntry. Import V8Drv1.V8Open. Import V8Drv1.V8Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x51dfb) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem u8_pins : @V8Main.pins (@mallocng_alloc_layout LU8).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU8] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LU8] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU8] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU8] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU8] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x31aa0 <= a)%Z -> (a + Z.of_nat n <= 0x51e68)%Z -> (a + Z.of_nat n <= 0x31acc \/ 0x31ad0 <= a)%Z ->
              (a + Z.of_nat n <= 0x51bb0 \/ 0x51dd0 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU8].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x51dfb) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x51dfb%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x51dfb%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x51dfb) + Z.of_nat 0)%Z with 0x51dfb%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x51e28%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LU8]. change (bv_unsigned (Z_to_bv 64 0x51df8) + 8)%Z with 0x51e00%Z.
        rewrite (LIBC 0x51e00%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x207d0)) with 0x207d0%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End V8Pins.

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Spec.
Module V8Closed.
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
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver.Spec.
Import V8Kit.
Import V8Pins.
Import V8Drv1.
Import V8LeptPinsI.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8Main.
(* [comment removed for export] *)







Import V8Kit.V8MallocLayout. Import V8Kit.V8Alloc. Import V8Kit.V8Sure.


Import V8Drv1.V8FuzzIface.

Import ListNotations.

Theorem u8_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Ubsan.M.loaded_segments
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@V8Main.ref_realizes_spec_pins _ _ u8_sure V8Pins.u8_pins (u8_fuzz_call u8_sure)).
Qed.
End V8Closed.
