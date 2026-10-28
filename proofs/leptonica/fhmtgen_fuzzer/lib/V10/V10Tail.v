(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10CL7a.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10CL8a.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10CL9a.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptDeser.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptPixCopyA.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptGrayA.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptFhmt.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptFhmtW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptHmtW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10_code_fhH.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LeptRoom10.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.
Module V10LeptFuzz.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.GrayACELib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptSel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptUb.
Import V10CL7a.
Import V10CL8a.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptCmapValid.
Import V10CL9a.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptDeser.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptPixCopy.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptGrayA.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptFhmt.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptFhmtW.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptHmtW.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10_code_fhH.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom10.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptSel_iface.

Import V10CL8a.V10LeptPixHdr. Import V10CL8a.V10LeptCmap.


Import V10CL9a.V10LeptPixDestroy.



Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ5 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).
Definition frameZ (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19)].

Section FuzzSegs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Ltac fz_prologue s ret regs SOK :=
    zv F_155b0 D_155b0 (Z_to_bv 64 (s - 80));
    stepST F_155b4 D_155b4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_155b8 D_155b8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_155bc D_155bc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_155c0 D_155c0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_155c4 D_155c4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
  Ltac fz_epilogue s ret r0 :=
    sn F_1567c D_1567c;
    stepLD8 F_15680 D_15680 ret; stepLD8 F_15684 D_15684 (getr r0 8); stepLD8 F_15688 D_15688 (getr r0 9);
    stepLD8 F_1568c D_1568c (getr r0 18); stepLD8 F_15690 D_15690 (getr r0 19);
    zv F_15694 D_15694 (Z_to_bv 64 s); stepret F_15698 D_15698 ret ltac:(bveq).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x156ac : word) m rom) (mkst regs' ret (FZ5 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19]%bv -> getr regs' x = getr regs x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FZ5. eexists. split.
    - fz_prologue s ret regs SOK.
      sn F_155c8 D_155c8. sn F_155cc D_155cc. stepb_tk F_155d0 D_155d0 ltac:(condZ).
      fz_epilogue s ret regs. apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma fz_A : forall regs m (s sz : Z) (dptr ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
    store_ok SEGS m (Z_to_bv 64 0x34e08) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x156ac : word) m rom)
                              (mkst regs' (0x26944 : word) (wbytes (FZ5 m s ret regs) (Z_to_bv 64 0x34e08) (word_to_le_bytes 8 (Z_to_bv 64 0x15798))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ getr regs' 1 = Z_to_bv 64 0x156ec /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FZ5. eexists. split.
    - fz_prologue s ret regs SOK.
      sn F_155c8 D_155c8. sn F_155cc D_155cc. stepb_ft F_155d0 D_155d0 ltac:(condZ).
      sn F_155d4 D_155d4. sn F_155d8 D_155d8. sn F_155dc D_155dc. sn F_155e0 D_155e0.
      stepb_tk F_157bc D_157bc ltac:(condZ).
      sn F_157c8 D_157c8.
      stepST F_157cc D_157cc (Z_to_bv 64 0x34e08) (Z_to_bv 64 0x15798) ltac:(store_ok_peel; exact SOKh).
      stepret F_157d0 D_157d0 (0x156e0 : word) ltac:(bveq).
      sn F_155e4 D_155e4. sn F_155e8 D_155e8. sn F_155ec D_155ec. sn F_26844 D_26844. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs r0 m (s : Z) (ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
    cellsZ m (frameZ s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x156ec : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret SOK CE H2 H10. unfold frameZ in CE. cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & C4 & C5 & _). eexists. split.
    - stepST F_155f0 D_155f0 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_155f4 D_155f4 ltac:(condZ).
      fz_epilogue s ret r0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x156ec : word) m rom) (mkst regs' (0x27be8 : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15700 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 18]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Hp Hp64 SOK H2 H10. eexists. split.
    - stepST F_155f0 D_155f0 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_155f4 D_155f4 ltac:(condZ).
      sn F_155f8 D_155f8. sn F_155fc D_155fc. sn F_15600 D_15600. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s sela : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 sela ->
    exists regs', msteps SEGS (mkst regs (0x15700 : word) m rom) (mkst regs' (0x27aa0 : word) (wbytes m (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 sela))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1570c /\ getr regs' 10 = Z_to_bv 64 sela /\ getr regs' 8 = Z_to_bv 64 sela
      /\ regs_agree (fun r => In r [1; 8]%list) regs regs'.
  Proof.
    intros regs m s sela Hs Hs64 SOK H2 H10. eexists. split.
    - sn F_15604 D_15604.
      stepST F_15608 D_15608 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 sela) ltac:(sok_in SOK).
      sn F_1560c D_1560c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_D : forall regs m (n pixs : Z),
    getr regs 10 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs', msteps SEGS (mkst regs (0x1570c : word) m rom) (mkst regs' (0x16c74 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1571c /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m n pixs H10 H18. eexists. split.
    - sn F_15610 D_15610. sn F_15614 D_15614. sn F_15618 D_15618. sn F_1561c D_1561c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall regs m (s copy : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 copy -> getr regs 9 = Z_to_bv 64 10 ->
    exists regs', msteps SEGS (mkst regs (0x1571c : word) m rom) (mkst regs' (0x1572c : word) (wbytes m (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 copy))) rom)
      /\ getr regs' 18 = Z_to_bv 64 copy /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [18; 19]%list) regs regs'.
  Proof.
    intros regs m s copy Hs Hs64 SOK H2 H10 H9. eexists. split.
    - stepST F_15620 D_15620 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 copy) ltac:(sok_in SOK).
      stepb_ft F_15624 D_15624 ltac:(condZ).
      sn F_15628 D_15628. sn F_1562c D_1562c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_L1 : forall regs m (sela i : Z),
    getr regs 8 = Z_to_bv 64 sela -> getr regs 19 = Z_to_bv 64 i ->
    exists regs', msteps SEGS (mkst regs (0x1572c : word) m rom) (mkst regs' (0x27aec : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15738 /\ getr regs' 10 = Z_to_bv 64 sela /\ getr regs' 11 = Z_to_bv 64 i
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sela i H8 H19. eexists. split.
    - sn F_15630 D_15630. sn F_15634 D_15634. sn F_15638 D_15638. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_L2 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x15738 : word) m rom) (mkst regs' (0x27b9c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1573c
      /\ regs_agree (fun r => In r [1]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_1563c D_1563c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_L3 : forall regs m (name copy : Z),
    getr regs 10 = Z_to_bv 64 name -> getr regs 18 = Z_to_bv 64 copy ->
    exists regs', msteps SEGS (mkst regs (0x1573c : word) m rom) (mkst regs' (0x282bc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1574c /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 copy /\ getr regs' 12 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m name copy H10 H18. eexists. split.
    - sn F_15640 D_15640. sn F_15644 D_15644. sn F_15648 D_15648. sn F_1564c D_1564c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_L4 : forall regs m (s r : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 r ->
    exists regs', msteps SEGS (mkst regs (0x1574c : word) m rom) (mkst regs' (0x1615c : word) (wbytes m (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 r))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15758 /\ getr regs' 10 = Z_to_bv 64 (s - 72)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s r Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_15650 D_15650 (Z_to_bv 64 (s - 72)) (Z_to_bv 64 r) ltac:(sok_in SOK).
      zv F_15654 D_15654 (Z_to_bv 64 (s - 72)). sn F_15658 D_15658. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_L5b : forall regs m (i : Z),
    (0 <= i)%Z -> (i + 1 < 10)%Z -> getr regs 9 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 i ->
    exists regs', msteps SEGS (mkst regs (0x15758 : word) m rom) (mkst regs' (0x1572c : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [19]%list) regs regs'.
  Proof.
    intros regs m i Hi Hi1 H9 H19. eexists. split.
    - stepat F_1565c D_1565c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity). stepb_tk F_15660 D_15660 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma fz_L5x : forall regs m (s i : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (i + 1 = 10)%Z -> getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 9 = Z_to_bv 64 10 -> getr regs 19 = Z_to_bv 64 i ->
    exists regs', msteps SEGS (mkst regs (0x15758 : word) m rom) (mkst regs' (0x1615c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15768 /\ getr regs' 10 = Z_to_bv 64 (s - 64)
      /\ regs_agree (fun r => In r [1; 10; 19]%list) regs regs'.
  Proof.
    intros regs m s i Hs Hs64 Hi H2 H9 H19. eexists. split.
    - stepat F_1565c D_1565c (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity). stepb_ft F_15660 D_15660 ltac:(condZ).
      zv F_15664 D_15664 (Z_to_bv 64 (s - 64)). sn F_15668 D_15668. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_G : forall regs m (s : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 80) ->
    exists regs', msteps SEGS (mkst regs (0x15768 : word) m rom) (mkst regs' (0x1615c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15770 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_1566c D_1566c (Z_to_bv 64 (s - 48)). sn F_15670 D_15670. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_H : forall regs m (s : Z),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 80) ->
    exists regs', msteps SEGS (mkst regs (0x15770 : word) m rom) (mkst regs' (0x26eac : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x15778 /\ getr regs' 10 = Z_to_bv 64 (s - 56)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_15674 D_15674 (Z_to_bv 64 (s - 56)). sn F_15678 D_15678. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_Z : forall regs r0 m (s : Z) (ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameZ s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 80) ->
    exists regs', msteps SEGS (mkst regs (0x15778 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameZ in CE. cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & C4 & C5 & _). eexists. split.
    - fz_epilogue s ret r0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.
End FuzzSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rebase.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure} {LL : LeptLayout} {PINS : @LeptPins AL LL}.

Definition rebase (C : lctx) (m : word -> option byte) (A : AS) : lctx :=
  LCTX (c_sp0 C) (c_argv C) (c_envp C) (c_top C) (c_vm C) m A.

Lemma Cok_rebase : forall C m A, Cok C -> Cok (rebase C m A).
Proof. intros C m A [T1 T2 T3 T4 T5]. constructor; cbn; assumption. Qed.

Lemma W_rebase : forall C A m md, W C A m md -> W (rebase C m A) A m md.
Proof.
  intros C A m md HW. destruct HW. constructor; cbn; try assumption.
  - intros a _ _ _ _ _. reflexivity.
  - intros q k L. exact L.
  - intros q k i _ _. reflexivity.
  - intros a D. right; right. exact D.
Qed.

Lemma W_unbase : forall C A1 m1 md1 A m md, W C A1 m1 md1 -> W (rebase C m1 A1) A m md -> W C A m md.
Proof.
  intros C A1 m1 md1 A m md W1 W2. destruct W1 as [I1 P1 E1 V1 WN1 CL1 H1 F1 K1 L1 D1]. destruct W2 as [I2 P2 E2 V2 WN2 CL2 H2 F2 K2 L2 D2].
  cbn in *. constructor; try assumption.
  - intros a N1 N2 N3 N4 N5. rewrite (F2 a N1 N2 N3 N4 N5). exact (F1 a N1 N2 N3 N4 N5).
  - intros q k L. exact (K2 q k (K1 q k L)).
  - intros q k i L Hi. rewrite (L2 q k i (K1 q k L) Hi). exact (L1 q k i L Hi).
  - intros a D. destruct (D1 a D) as [X|[X|X]]; [left; exact X | right; left; exact X |]. exact (D2 a X).
Qed.

(* [comment removed for export] *)
Lemma W_livk0 : forall C A m md, W C A m md -> LIVK (c_A0 C) (c_m0 C) m.
Proof. intros C A m md HW q k i L Hi. exact (w_live0 _ _ _ _ HW q k i L Hi). Qed.
Lemma W_sub0' : forall C A m md, W C A m md -> sub_live (c_A0 C) A.
Proof. intros C A m md HW q k L. exact (w_keep _ _ _ _ HW q k L). Qed.
End Rebase.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameZ.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma cells_FZ5 : forall m s ret regs, (80 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FZ5 m s ret regs) (frameZ s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frameZ, FZ5. cbn [cellsZ]. repeat split; rdn_solve. Qed.
Lemma frameZ_bounds : forall s ret r0, (80 <= s)%Z -> (s < 2 ^ 64)%Z -> Forall (fun av => s - 40 <= fst av /\ fst av + 8 <= s)%Z (frameZ s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameZ. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.
Lemma FZ5_out : forall m s ret regs (x : word), (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 40 <= u x < s)%Z -> FZ5 m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FZ5.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.
Lemma cellsF_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 40)%Z -> (80 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameZ s ret r0) -> cellsZ m' (frameZ s ret r0).
Proof.
  intros C s' m m' s ret r0 CK F H1 H2 Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameZ_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.
Lemma cellsF_out : forall m m' (lo hi : Z) s ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 40 \/ s <= lo)%Z -> (80 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameZ s ret r0) -> cellsZ m' (frameZ s ret r0).
Proof.
  intros m m' lo hi s ret r0 OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (frameZ_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.
End FrameZ.
End V10LeptFuzz.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10Drv1.
Module V10LeptFuzzMain.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.GrayACELib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptSel.
Import V10Drv1.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptUb.
Import V10CL7a.
Import V10CL8a.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptCmapValid.
Import V10CL9a.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptDeser.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptPixCopy.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptGrayA.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptFhmt.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptFhmtW.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptHmtW.
Import V10LeptFuzz.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptRoom10.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V10Drv1.V10FuzzIface.


Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptSel_iface.

Import V10CL8a.V10LeptPixHdr. Import V10CL8a.V10LeptCmap.


Import V10CL9a.V10LeptPixDestroy.



Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rok := red; apply bv_eq; reflexivity.
(* [comment removed for export] *)
Abbreviation DRz := ([3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list (bv 5)).
Ltac drz_solve := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BlkDec.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma ex_below_dec : forall (P : Z -> Prop) (n : Z), (forall i, P i \/ ~ P i) ->
  (exists i, (0 <= i < n)%Z /\ P i) \/ ~ (exists i, (0 <= i < n)%Z /\ P i).
Proof.
  intros P n D.
  assert (G : forall k : nat, (exists i, (0 <= i < Z.of_nat k)%Z /\ P i) \/ ~ (exists i, (0 <= i < Z.of_nat k)%Z /\ P i)).
  { induction k as [|k IH]; [right; intros (i & Hi & _); lia|].
    destruct IH as [(i & Hi & Pi)|N]; [left; exists i; split; [lia | exact Pi]|].
    destruct (D (Z.of_nat k)) as [Pk|NPk]; [left; exists (Z.of_nat k); split; [lia | exact Pk]|].
    right. intros (i & Hi & Pi). destruct (Z.eq_dec i (Z.of_nat k)) as [E|NE]; [rewrite E in Pi; exact (NPk Pi) | apply N; exists i; split; [lia | exact Pi]]. }
  destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [right; intros (i & Hi & _); lia|].
  replace n with (Z.of_nat (Z.to_nat n)) by lia. apply G.
Qed.

Lemma sel_blk_dec : forall sel v p, sel_blk sel v p \/ ~ sel_blk sel v p.
Proof.
  intros sel v p. unfold sel_blk.
  destruct (Z.eq_dec p sel) as [E|N1]; [left; left; exact E|].
  destruct (Z.eq_dec p (v_data v)) as [E|N2]; [left; right; left; exact E|].
  destruct (ex_below_dec (fun i => p = v_rows v i) (v_sy v)) as [E|N3].
  { intros i. destruct (Z.eq_dec p (v_rows v i)) as [X|X]; [left | right]; exact X. }
  - left; right; right; exact E.
  - right. intros [X|[X|X]]; contradiction.
Qed.

Lemma seln_blk_dec : forall sel v p, seln_blk sel v p \/ ~ seln_blk sel v p.
Proof.
  intros sel v p. unfold seln_blk. destruct (sel_blk_dec sel v p) as [E|N1]; [left; left; exact E|].
  destruct (Z.eq_dec p (v_name v)) as [E|N2]; [left; right; exact E | right; intros [X|X]; contradiction].
Qed.

Lemma sela_blk_dec : forall sela arr n sels vs p, sela_blk sela arr n sels vs p \/ ~ sela_blk sela arr n sels vs p.
Proof.
  intros sela arr n sels vs p. unfold sela_blk.
  destruct (Z.eq_dec p sela) as [E|N1]; [left; left; exact E|].
  destruct (Z.eq_dec p arr) as [E|N2]; [left; right; left; exact E|].
  destruct (ex_below_dec (fun i => seln_blk (sels i) (vs i) p) n (fun i => seln_blk_dec (sels i) (vs i) p)) as [E|N3].
  - left; right; right; exact E.
  - right. intros [X|[X|X]]; contradiction.
Qed.

Lemma sela_blk_live_all : forall T A m sela arr n sels vs nms p, sela_at T A m sela arr n sels vs nms -> sela_blk sela arr n sels vs p ->
  exists k, live A (Z_to_bv 64 p) = Some k /\ (0 <= k)%Z /\ (1 <= p)%Z /\ (p + k <= T)%Z.
Proof.
  intros T A m sela arr n sels vs nms p SA [E | [E | (i & Hi & HB)]].
  - subst p. destruct SA as (_ & (G1 & G2 & _) & Ls & _). exists 16%Z. repeat split; [exact Ls | lia | lia | lia].
  - subst p. destruct SA as (_ & _ & _ & _ & (G1 & G2 & _) & La & _). exists 400%Z. repeat split; [exact La | lia | lia | lia].
  - exact (sela_blk_live T A m sela arr n sels vs nms i p SA Hi HB).
Qed.

(* [comment removed for export] *)
Lemma live_back : forall (A A1 A2 A3 A4 A5 A6 : AS) (Bs Ba Bc : word -> Prop),
  (forall q, Bs q \/ ~ Bs q) -> (forall q, Ba q \/ ~ Ba q) -> (forall q, Bc q \/ ~ Bc q) ->
  (forall q, Bs q -> live A q = None) -> (forall q, ~ Bs q -> live A1 q = live A q) ->
  (forall q, Ba q -> live A q = None) -> (forall q, ~ Ba q -> live A2 q = live A1 q) ->
  (forall q, Bc q -> live A2 q = None) -> (forall q, ~ Bc q -> live A3 q = live A2 q) ->
  (forall q, Bc q -> live A4 q = None) -> (forall q, ~ Bc q -> live A4 q = live A3 q) ->
  (forall q, Bs q -> live A5 q = None) -> (forall q, ~ Bs q -> live A5 q = live A4 q) ->
  (forall q, Ba q -> live A6 q = None) -> (forall q, ~ Ba q -> live A6 q = live A5 q) ->
  forall q, live A6 q = live A q.
Proof.
  intros A A1 A2 A3 A4 A5 A6 Bs Ba Bc Ds Da Dc S0 SE A0 AE C2 CE C4 C4E S5 S5E A6' A6E q.
  destruct (Da q) as [Ha|Na]; [rewrite (A6' q Ha), (A0 q Ha); reflexivity|].
  rewrite (A6E q Na).
  destruct (Ds q) as [Hs|Ns]; [rewrite (S5 q Hs), (S0 q Hs); reflexivity|].
  rewrite (S5E q Ns).
  destruct (Dc q) as [Hc|Nc].
  - rewrite (C4 q Hc). rewrite <- (SE q Ns), <- (AE q Na). symmetry. exact (C2 q Hc).
  - rewrite (C4E q Nc), (CE q Nc), (AE q Na). exact (SE q Ns).
Qed.

(* [comment removed for export] *)
Lemma res_oown_d : forall {PINS : @LeptPins AL LLU16} C A2 A3 m4 (r5 : bvmap 5 word) w' h' d' cv',
  (0 < 4 * (wpl_of w' d' * h'))%Z ->
  ( (getr r5 10 = Z_to_bv 64 0 /\ forall q, live A3 q = live A2 q)
    \/ (exists pixd cd data, getr r5 10 = Z_to_bv 64 pixd /\ pixt_new C A2 A3 m4 pixd w' h' d' cd data cv') ) ->
  exists p3 cd3 data3 ad3, getr r5 10 = Z_to_bv 64 p3 /\ oown C A2 A3 m4 p3 w' h' d' cd3 data3 ad3 (c_d cv') (c_nalloc cv') (c_n cv') /\
     (forall q, ~ oblk p3 data3 cd3 ad3 q -> live A3 q = live A2 q).
Proof.
  intros PINS C A2 A3 m4 r5 w' h' d' cv' Rpos [[R10 LEQ] | (pixd & cd & data & R10 & PT)].
  - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact R10|]. split; [left; reflexivity|]. intros q _. apply LEQ.
  - destruct (pixt_new_pown _ _ _ _ _ _ _ _ _ _ _ PT Rpos) as (ad & OWN & LEQ).
    exists pixd, cd, data, ad. split; [exact R10|]. split; [right; exact OWN|].
    intros q NB. apply LEQ. intros B. apply NB. split; [destruct OWN as (Gp & _); lia | exact B].
Qed.
End BlkDec.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Hypothesis HMT : pixHMTDwa_1_contract.
Hypothesis SDES : selaDestroy_contract.
Hypothesis GSEL : selaGetSel_run.
Hypothesis GNAME : selGetName_run.

Variables (C : lctx) (A A1 A2 A3 : AS) (m3 : word -> option byte) (md0 : Model) (vm3 : VmMaps).
Variables (s : Z) (ret : word) (regs : bvmap 5 word) (S : TSet).
Variables (pixs w h d cm datas : Z) (cv : cmapv) (sela arr : Z) (sels : Z -> Z) (vs : Z -> selv) (copy cd data ad : Z).
Variables (kF bF : Z).
Let C1 := rebase C m3 A3.

Hypothesis CK : Cok C.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Htop : c_top C = s.
Hypothesis HA0 : c_A0 C = A.
Hypothesis Hret : ret_ok ret.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x45480.
Hypothesis HW3 : W C A3 m3 (with_vmmaps vm3 md0).
(* [comment removed for export] *)
Hypothesis PXs : PIXat m3 pixs (hdv w h d cm datas).
Hypothesis HOK : hdr_ok w h d.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Lps : live A3 (Z_to_bv 64 pixs) = Some 64%Z.
Hypothesis Lds : live A3 (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z.
Hypothesis NEsd : datas <> pixs.
Hypothesis HCM : boxed (cm = 0%Z \/ (CMAPat m3 cm cv /\ cmap_ok cv /\ live A3 (Z_to_bv 64 cm) = Some 24%Z /\ live A3 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                  cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ datas <> cm /\ datas <> c_arr cv)).
Hypothesis S0 : forall q, pblk pixs datas cm (c_arr cv) q -> live A q = None.
Hypothesis S1 : forall q, pblk pixs datas cm (c_arr cv) q -> exists n, live A1 q = Some n.
Hypothesis SE : forall q, ~ pblk pixs datas cm (c_arr cv) q -> live A1 q = live A q.
(* [comment removed for export] *)
Hypothesis SHM : sela_hm (alloc_top (c_vm C)) A3 m3 sela arr sels vs.
Hypothesis SOFF0 : sela_off A sela arr 10 sels vs.
Hypothesis SOFF1 : sela_off A1 sela arr 10 sels vs.
Hypothesis SLIV2 : forall p, sela_blk sela arr 10 sels vs p -> exists n, live A2 (Z_to_bv 64 p) = Some n.
Hypothesis SONLY : sela_only A1 A2 sela arr 10 sels vs.
(* [comment removed for export] *)
Hypothesis OOc : oown C A2 A3 m3 copy w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv).
Hypothesis CE3 : forall q, ~ oblk copy data cd ad q -> live A3 q = live A2 q.
(* [comment removed for export] *)
Hypothesis CEZ : cellsZ m3 (frameZ s ret regs).
Hypothesis R48 : rdn SEGS m3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs).
Hypothesis R56 : rdn SEGS m3 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela).
Hypothesis R64 : rdn SEGS m3 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 copy).
(* [comment removed for export] *)
Hypothesis HkF : (0 <= kF)%Z.
Hypothesis HbF : (0 <= bF)%Z.
Hypothesis KF : forall A' m' vm' r' k' b', W C A' m' (with_vmmaps vm' md0) -> (forall q, live A' q = live A q) ->
    getr r' 10 = Z_to_bv 64 0 -> cs_kept regs r' -> aroom A' vm' k' b' -> (kF <= k')%Z -> (bF <= b')%Z ->
    realizes SEGS (mkCfg (mkst r' ret m' al_rom) (with_vmmaps vm' md0)) S.

Lemma CK1 : Cok C1. Proof. exact (Cok_rebase C m3 A3 CK). Qed.

Lemma RBpos : (0 <= RB10_hmt d w h)%Z.
Proof. destruct HOK as (_ & Hw2 & Hh2 & _). exact (proj1 (RB10_hmt_le d w h ltac:(lia) ltac:(lia))). Qed.

(* [comment removed for export] *)
Lemma sblk_range : forall p, sela_blk sela arr 10 sels vs p -> (0 <= p < 2 ^ 64)%Z.
Proof.
  intros p Bp. destruct (sela_blk_live_all _ _ _ _ _ _ _ _ _ p (proj1 SHM) Bp) as (k & _ & Hk & Hp & HT).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. lia.
Qed.
Lemma D_as : forall p, sela_blk sela arr 10 sels vs p -> ~ pblk pixs datas cm (c_arr cv) (Z_to_bv 64 p).
Proof. intros p Bp B. destruct (S1 _ B) as [n Ln]. rewrite (SOFF1 p Bp) in Ln. discriminate. Qed.
Lemma D_ac : forall p, sela_blk sela arr 10 sels vs p -> ~ oblk copy data cd ad (Z_to_bv 64 p).
Proof. intros p Bp B. destruct (SLIV2 p Bp) as [n Ln]. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc _ B) in Ln. discriminate. Qed.
Lemma D_sc : forall q, pblk pixs datas cm (c_arr cv) q -> ~ oblk copy data cd ad q.
Proof.
  intros q Bq B. destruct (S1 _ Bq) as [n Ln].
  rewrite <- (SONLY q) in Ln; [rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc _ B) in Ln; discriminate|].
  intros p Bp E. subst q. exact (D_as p Bp Bq).
Qed.
(* [comment removed for export] *)
Definition Ba (q : word) : Prop := sela_blk sela arr 10 sels vs (u q).
Lemma Ba_off : forall X, sela_off X sela arr 10 sels vs -> forall q, Ba q -> live X q = None.
Proof. intros X SO q B. rewrite <- (zbv_self q). exact (SO (u q) B). Qed.
Lemma Ba_only : forall X X', sela_only X X' sela arr 10 sels vs -> forall q, ~ Ba q -> live X' q = live X q.
Proof.
  intros X X' SO q NB. apply SO. intros p Bp E. apply NB. unfold Ba. subst q. pose proof (sblk_range p Bp) as Rp. rewrite u_Z2bv by lia. exact Bp.
Qed.

(* [comment removed for export] *)
Lemma later : forall Ak mk mdk, W C1 Ak mk mdk -> FRM C1 (s - 64) m3 mk -> (forall q, live Ak q = live A3 q) ->
  cellsZ mk (frameZ s ret regs) /\
  rdn SEGS mk (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs) /\
  rdn SEGS mk (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela) /\
  rdn SEGS mk (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 copy) /\
  sela_hm (alloc_top (c_vm C)) Ak mk sela arr sels vs /\
  oown C A2 Ak mk copy w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv) /\
  PIXat mk pixs (hdv w h d cm datas) /\ (cm <> 0%Z -> CMAPat mk cm cv).
Proof.
  intros Ak mk mdk HWk Fk LQk.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. rewrite Htop in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (W_livk0 C1 Ak mk mdk HWk) as LK. cbn [C1 rebase c_A0 c_m0] in LK.
  pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A3 m3 _ (Z_to_bv 64 pixs) 64 CK HW3 Lps ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  split; [apply (cellsF_frm C1 (s - 64) m3 mk s ret regs CK1 Fk); [cbn; lia | lia | lia | lia | exact CEZ]|].
  split; [apply (cell_frm C1 (s - 64) m3 mk); [exact CK1 | exact Fk | cbn; lia | lia | lia | exact R48]|].
  split; [apply (cell_frm C1 (s - 64) m3 mk); [exact CK1 | exact Fk | cbn; lia | lia | lia | exact R56]|].
  split; [apply (cell_frm C1 (s - 64) m3 mk); [exact CK1 | exact Fk | cbn; lia | lia | lia | exact R64]|].
  split; [apply (sela_hm_keep _ A3 Ak m3 mk); [lia | exact SHM | apply sub_live_eq; exact LQk | exact LK]|].
  split; [exact (oown_keep C A2 A3 Ak A3 m3 mk _ _ _ _ _ _ _ _ _ _ OOc (fun q _ => LQk q) (fun _ _ => eq_refl) LK)|].
  split.
  - apply (PIXat_frame m3); [exact PXs|]. intros x Hx. exact (LIVK_at A3 m3 mk pixs 64 x LK Lps ltac:(lia) ltac:(lia) Hx).
  - intros NZ. destruct (box_e _ HCM) as [Z0 | (CM & _ & Lc & _)]; [exfalso; exact (NZ Z0)|]. pose proof CM as (Hc0 & Hc64 & _).
    apply (CMAPat_frame m3); [exact CM|]. intros x Hx. exact (LIVK_at A3 m3 mk cm 24 x LK Lc ltac:(lia) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Lemma FRM_win_write : forall mk (a : word) bs, FRM C1 (s - 64) m3 mk ->
  (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s - 64)%Z -> FRM C1 (s - 64) m3 (wbytes mk a bs).
Proof.
  intros mk a bs F Hlo Hhi. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  eapply FRM_trans; [exact F|]. intros x _ _ _ _ N5. unfold scratch in N5. cbn in N5. apply wbytes_outside; lia.
Qed.

(* [comment removed for export] *)
Definition rinv (i : Z) : Prop :=
  forall Ak mk vmk r k b, W C1 Ak mk (with_vmmaps vmk md0) -> aroom Ak vmk k b ->
    (kF + 12 * (10 - i) <= k)%Z -> (bF + (10 - i) * RB10_hmt d w h <= b)%Z ->
    FRM C1 (s - 64) m3 mk -> (forall q, live Ak q = live A3 q) ->
    getr r 2 = Z_to_bv 64 (s - 80) -> getr r 8 = Z_to_bv 64 sela -> getr r 9 = Z_to_bv 64 10 -> getr r 18 = Z_to_bv 64 copy ->
    getr r 19 = Z_to_bv 64 i -> (forall x, In x DRz -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x1572c : word) mk al_rom) (with_vmmaps vmk md0)) S.
Definition xinv : Prop :=
  forall Ak mk vmk r k b, W C1 Ak mk (with_vmmaps vmk md0) -> aroom Ak vmk k b -> (kF <= k)%Z -> (bF <= b)%Z ->
    FRM C1 (s - 64) m3 mk -> (forall q, live Ak q = live A3 q) ->
    getr r 2 = Z_to_bv 64 (s - 80) -> getr r 1 = Z_to_bv 64 0x15768 -> getr r 10 = Z_to_bv 64 (s - 64) ->
    (forall x, In x DRz -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x1615c : word) mk al_rom) (with_vmmaps vmk md0)) S.

(* [comment removed for export] *)
Lemma round_tail : forall i X A' m' vm' r' k' b' (rr cdr datar adr : Z),
  (0 <= i < 10)%Z -> (i + 1 < 10 -> rinv (i + 1))%Z -> (i + 1 = 10 -> xinv)%Z ->
  W C1 A' m' (with_vmmaps vm' md0) -> aroom A' vm' k' b' ->
  (kF + 12 * (10 - (i + 1)) <= k')%Z -> (bF + (10 - (i + 1)) * RB10_hmt d w h <= b')%Z ->
  FRM C1 (s - 64) m3 m' ->
  oown C1 X A' m' rr w h 1 cdr datar adr (c_d cv) (c_nalloc cv) (c_n cv) ->
  (forall q, ~ oblk rr datar cdr adr q -> live A' q = live A3 q) ->
  getr r' 2 = Z_to_bv 64 (s - 80) -> getr r' 10 = Z_to_bv 64 rr -> getr r' 8 = Z_to_bv 64 sela -> getr r' 9 = Z_to_bv 64 10 ->
  getr r' 18 = Z_to_bv 64 copy -> getr r' 19 = Z_to_bv 64 i -> (forall x, In x DRz -> getr r' x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r' (0x1574c : word) m' al_rom) (with_vmmaps vm' md0)) S.
Proof.
  intros i X A' m' vm' r' k' b' rr cdr datar adr Hi NXT XIT HW' Hrm' Hk' Hb' F' OOr LEQr Q2 Q10 Q8 Q9 Q18 Q19 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. rewrite Htop in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof CK1 as CK1'. pose proof RBpos as HBpos. assert (Etop1 : c_top C1 = s) by exact Htop.
  assert (HBn : (0 <= (10 - (i + 1)) * RB10_hmt d w h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOr) as Hrr.
  assert (Hs80 : (80 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  (* [comment removed for export] *)
  destruct (fz_L4 al_rom r' m' s rr Hs80 Hs264 (W_sok_win C1 A' m' _ (s - 72) 8 CK1' HW' ltac:(cbn; lia) ltac:(cbn; lia)) Q2 Q10) as (r1 & RUN1 & E1 & E10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN1 |]. clear RUN1.
  set (M := wbytes m' (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 rr))).
  assert (WPM : W C1 A' M (with_vmmaps vm' md0) /\ POSTM C1 A' (s - 64) m' M) by (subst M; wp_win CK1').
  destruct WPM as [HWM PMM].
  assert (FM : FRM C1 (s - 64) m3 M) by (subst M; apply FRM_win_write; [exact F' | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  assert (R72 : rdn SEGS M (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 rr)) by (subst M; apply cell_wr; lia).
  pose proof (oown_keep C1 X A' A' A' m' M _ _ _ _ _ _ _ _ _ _ OOr (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PMM)) as OOr'.
  apply (pixDestroy_opt_W C1 X A' M (with_vmmaps vm' md0) r1 (s - 80) (s - 72) rr w h 1 cdr datar adr (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 0x15758) S CK1' HWM
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia)
           E1 ltac:(rok) ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) E10 R72 OOr').
  intros A'' m'' vm'' r2 HW'' CS2 DEAD LEQ PM'' OUT'' RT''. rewrite with_vmmaps_twice in HW'' |- *. rewrite with_vmmaps_vmmaps in RT''.
  replace (Z_to_bv 64 0x15758) with (0x15758 : word) by (apply bv_eq; reflexivity).
  replace (s - 72 + 8)%Z with (s - 64)%Z in PM'' by lia.
  pose proof (RT'' k' b' Hrm' ltac:(lia) ltac:(lia)) as Hrm''. rewrite !Z.sub_0_r in Hrm''.
  assert (LQ'' : forall q, live A'' q = live A3 q).
  { intros q. destruct (oblk_dec rr datar cdr adr q) as [B|NB]; [| rewrite (LEQ q NB); exact (LEQr q NB)].
    rewrite (DEAD q B). symmetry. destruct OOr as [P0 | OWN]; [destruct B as [NZ _]; contradiction|].
    destruct OWN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _). destruct B as [_ B]. exact (proj2 (FR q B)). }
  assert (F'' : FRM C1 (s - 64) m3 m'') by (eapply FRM_trans; [exact FM | exact (proj1 PM'')]).
  destruct (Z_lt_ge_dec (i + 1) 10) as [LT|GE].
  - destruct (fz_L5b al_rom r2 m'' i ltac:(lia) LT ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN3 |]. clear RUN3.
    apply (NXT LT A'' m'' vm'' r3 k' b' HW'' Hrm'' Hk' Hb' F'' LQ''); [csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | exact V19 | drz_solve].
  - assert (EX : (i + 1 = 10)%Z) by lia.
    destruct (fz_L5x al_rom r2 m'' s i Hs80 Hs264 EX ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN3 |]. clear RUN3.
    replace (10 - (i + 1))%Z with 0%Z in Hk', Hb' by lia.
    apply (XIT EX A'' m'' vm'' r3 k' b' HW'' Hrm'' ltac:(lia) ltac:(lia) F'' LQ''); [csr; reflexivity | exact V1 | exact V10 | drz_solve].
Qed.

(* [comment removed for export] *)
Lemma round_W : forall i, (0 <= i < 10)%Z -> (i + 1 < 10 -> rinv (i + 1))%Z -> (i + 1 = 10 -> xinv)%Z -> rinv i.
Proof.
  intros i Hi NXT XIT. unfold rinv. intros Ak mk vmk r k b HWk Hrmk Hk Hb Fk LQk Q2 Q8 Q9 Q18 Q19 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. rewrite Htop in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof CK1 as CK1'. pose proof RBpos as HBpos.
  assert (HBn : (0 <= (10 - (i + 1)) * RB10_hmt d w h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (EB : ((10 - i) * RB10_hmt d w h = (10 - (i + 1)) * RB10_hmt d w h + RB10_hmt d w h)%Z) by ring.
  destruct (later Ak mk _ HWk Fk LQk) as (CEk & R48k & R56k & R64k & SHMk & OOk & PXk & CMk).
  pose proof (proj1 SHMk) as (Hn & Bs & Ls & Rs & Bar & La & NEa & CELLS & DIST).
  destruct (CELLS i Hi) as (Bi & SAi & NAi & _ & _).
  pose proof SAi as (Hsy & Hsx & Bsel & Lsel & Rsel & _).
  destruct Bs as (Gs & Ts & ALs). destruct Bar as (Ga & Ta & ALa). pose proof Bsel as (Gsel & Tsel & ALsel).
  (* [comment removed for export] *)
  destruct (fz_L1 al_rom r mk sela i Q8 Q19) as (r1 & RUN1 & E1 & E10 & E11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |]. clear RUN1.
  replace (0x27aec : word) with (Z_to_bv 64 PC_selaGetSel) by (apply bv_eq; reflexivity).
  destruct (GSEL al_rom r1 mk sela 10%Z 50%Z arr i (sels i) (Z_to_bv 64 0x15738) Rs ltac:(lia) (bok_mod8 _ _ 16 (conj Gs (conj Ts ALs))) Hi ltac:(lia) ltac:(lia) ltac:(lia)
              (bok_mod8 _ _ 400 (conj Ga (conj Ta ALa))) Bi ltac:(lia) E1 ltac:(rok) E10 E11) as (r2 & RUN2 & G10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN2 |]. clear RUN2.
  replace (Z_to_bv 64 0x15738) with (0x15738 : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  destruct (fz_L2 al_rom r2 mk) as (r3 & RUN3 & F1 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN3 |]. clear RUN3.
  replace (0x27b9c : word) with (Z_to_bv 64 PC_selGetName) by (apply bv_eq; reflexivity).
  destruct (GNAME al_rom r3 mk (sels i) _ _ _ _ _ (v_name (vs i)) (Z_to_bv 64 0x1573c) Rsel ltac:(lia) (bok_mod8 _ _ _ Bsel) F1 ltac:(rok) ltac:(csr; reflexivity))
    as (r4 & RUN4 & N10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN4 |]. clear RUN4.
  replace (Z_to_bv 64 0x1573c) with (0x1573c : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  destruct (fz_L3 al_rom r4 mk (v_name (vs i)) copy N10 ltac:(csr; reflexivity)) as (r5 & RUN5 & P1 & P10 & P11 & P12 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN5 |]. clear RUN5.
  replace (0x282bc : word) with (Z_to_bv 64 PC_pixHMTDwa_1) by (apply bv_eq; reflexivity).
  assert (P2 : getr r5 2 = Z_to_bv 64 (s - 80)) by (csr; reflexivity).
  assert (NOROOM : forall m' r6, W C1 Ak m' (with_vmmaps vmk md0) -> cs_kept r5 r6 -> POSTM C1 Ak (s - 80) mk m' -> getr r6 10 = Z_to_bv 64 0 ->
            realizes SEGS (mkCfg (mkst r6 (Z_to_bv 64 0x1574c) m' al_rom) (with_vmmaps vmk md0)) S).
  { intros m' r6 HW' CS6 PM' A10. replace (Z_to_bv 64 0x1574c) with (0x1574c : word) by (apply bv_eq; reflexivity).
    apply (round_tail i Ak Ak m' vmk r6 k b 0 0 0 0 Hi NXT XIT HW' Hrmk ltac:(lia) ltac:(lia)).
    - eapply FRM_trans; [exact Fk | eapply FRM_mono; [exact (proj1 PM') | lia]].
    - left; reflexivity.
    - intros q _. apply LQk.
    - csr; reflexivity.
    - exact A10.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - csr; reflexivity.
    - drz_solve. }
  destruct OOk as [C0 | OWNc].
  - (* [comment removed for export] *)
    rewrite C0 in P11.
    exact (pixHMTDwa_1_null_W C1 Ak mk _ r5 (s - 80)%Z (v_name (vs i)) (Z_to_bv 64 0x1574c) S CK1' HWk P2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold HMT_STACK, FHG_STACK, LSF; lia) ltac:(cbn; lia) P1 ltac:(rok) P10 P11 P12 NOROOM).
  - pose proof OWNc as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PXc & Lpc & Ldc & FRc & CMRc).
    destruct (Z.eq_dec d 1) as [Ed|Nd].
    + (* [comment removed for export] *)
      pose proof PXc as PXc1. pose proof Ldc as Ldc1. pose proof HOK as HOK1. rewrite Ed in PXc1, Ldc1, HOK1.
      pose proof Hb as Hb1. rewrite EB in Hb1. rewrite Ed in Hb1. pose proof HBn as HBn1. rewrite Ed in HBn1. pose proof HBpos as HBpos1. rewrite Ed in HBpos1.
      pose proof Hrmk as Hrmk1. rewrite <- (with_vmmaps_vmmaps vmk md0) in Hrmk1.
      assert (K12 : RK10_hmt 1 = 12%Z) by reflexivity.
      apply (HMT C1 Ak mk (with_vmmaps vmk md0) r5 (s - 80)%Z copy w h cd data (v_name (vs i)) i (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) (Z_to_bv 64 0x1574c) S CK1' HWk P2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold HMT_STACK, FHG_STACK, LSF; lia) ltac:(cbn; lia) P1 ltac:(rok)
               ltac:(csr; reflexivity) P10 P11 P12 PXc1 HOK1 Hw Hh Lpc Ldc1 (pown_cm_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNc) Hi NAi
               k b Hrmk1 ltac:(rewrite K12; lia) ltac:(lia)).
      cbn [c_d c_nalloc c_n].
      intros A' m' vm' r6 HW' CS6 PM' RES Hrm'. rewrite with_vmmaps_twice in HW' |- *.
      replace (Z_to_bv 64 0x1574c) with (0x1574c : word) by (apply bv_eq; reflexivity).
      rewrite K12 in Hrm'.
      assert (F' : FRM C1 (s - 64) m3 m') by (eapply FRM_trans; [exact Fk | eapply FRM_mono; [exact (proj1 PM') | lia]]).
      destruct RES as [[A10 LEQ'] | (pixd & cdr & datar & adr & A10 & OWNr & LEQ')].
      * apply (round_tail i Ak A' m' vm' r6 (k - 12) (b - RB10_hmt 1 w h) 0 0 0 0 Hi NXT XIT HW' Hrm' ltac:(lia) ltac:(rewrite Ed; lia) F').
        -- left; reflexivity.
        -- intros q _. rewrite LEQ'. apply LQk.
        -- csr; reflexivity.
        -- exact A10.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- drz_solve.
      * assert (NZr : pixd <> 0%Z) by (destruct OWNr as (Gr & _); lia).
        apply (round_tail i Ak A' m' vm' r6 (k - 12) (b - RB10_hmt 1 w h) pixd cdr datar adr Hi NXT XIT HW' Hrm' ltac:(lia) ltac:(rewrite Ed; lia) F').
        -- right; exact OWNr.
        -- intros q NB. rewrite (LEQ' q (fun B => NB (conj NZr B))). apply LQk.
        -- csr; reflexivity.
        -- exact A10.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- drz_solve.
    + (* [comment removed for export] *)
      pose proof HOK as (DV & _). pose proof (dval_range d DV) as Hd32.
      exact (pixHMTDwa_1_d_W C1 Ak mk _ r5 (s - 80)%Z copy (v_name (vs i)) (hdv w h d cd data) (Z_to_bv 64 0x1574c) S CK1' HWk P2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold HMT_STACK, FHG_STACK, LSF; lia) ltac:(cbn; lia) P1 ltac:(rok) P10 P11 P12
               PXc Lpc ltac:(cbn [p_d hdv]; lia) ltac:(cbn [p_d hdv]; exact Nd) NOROOM).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PHX : xinv.
Proof.
  unfold xinv. intros Ak mk vmk r k b HWk Hrmk Hk Hb Fk LQk Q2 Q1 Q10 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. rewrite Htop in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs80 : (80 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  destruct (later Ak mk _ HWk Fk LQk) as (CEk & R48k & R56k & R64k & SHMk & OOk & PXk & CMk).
  pose proof (W_unbase C A3 m3 _ Ak mk _ HW3 HWk) as HWx.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  assert (Rpos : (0 < 4 * (wpl_of w d * h))%Z) by (assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  pose proof PXs as (Hp0 & Hp64 & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdv] in Rds.
  destruct (blk_range C A3 m3 _ (Z_to_bv 64 datas) _ CK HW3 Lds Rpos) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  apply (pixDestroy_opt_W C A2 Ak mk (with_vmmaps vmk md0) r (s - 80) (s - 64) copy w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 0x15768) S CK HWx
           Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           Q1 ltac:(rok) ltac:(rewrite (RR 4) by in_lit; exact H4) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) Q10 R64k OOk).
  intros A4 m4 vm4 r4 HW4 CS4 DEAD4 LEQ4 PM4 OUT4 RT4. rewrite with_vmmaps_twice in HW4 |- *. rewrite with_vmmaps_vmmaps in RT4.
  replace (Z_to_bv 64 0x15768) with (0x15768 : word) by (apply bv_eq; reflexivity).
  replace (s - 64 + 8)%Z with (s - 56)%Z in PM4 by lia.
  pose proof (RT4 k b Hrmk ltac:(lia) ltac:(lia)) as Hrm4. rewrite !Z.sub_0_r in Hrm4.
  assert (CE4 : cellsZ m4 (frameZ s ret regs)) by (apply (cellsF_frm C (s - 56) mk m4 s ret regs CK (proj1 PM4)); [lia | lia | lia | lia | exact CEk]).
  assert (R48' : rdn SEGS m4 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs)) by (apply (cell_frm C (s - 56) mk m4); [exact CK | exact (proj1 PM4) | lia | lia | lia | exact R48k]).
  assert (R56' : rdn SEGS m4 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela)) by (apply (cell_frm C (s - 56) mk m4); [exact CK | exact (proj1 PM4) | lia | lia | lia | exact R56k]).
  assert (SHM4 : sela_hm (alloc_top (c_vm C)) A4 m4 sela arr sels vs).
  { apply (sela_hm_keep_blk _ Ak A4 A4 mk m4); [lia | exact SHMk | intros p Bp; exact (LEQ4 _ (D_ac p Bp)) | intros p Bp; exact (LEQ4 _ (D_ac p Bp)) | exact (proj2 PM4)]. }
  assert (LS4 : forall q, pblk pixs datas cm (c_arr cv) q -> live A4 q = live A3 q) by (intros q B; rewrite (LEQ4 q (D_sc q B)); apply LQk).
  assert (Lps4 : live A4 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LS4 _ (or_introl eq_refl)); exact Lps).
  assert (Lds4 : live A4 (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z) by (rewrite (LS4 _ (or_intror (or_introl eq_refl))); exact Lds).
  assert (PX4 : PIXat m4 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame mk); [exact PXk|]. intros x Hx. exact (LIVK_at A4 mk m4 pixs 64 x (proj2 PM4) Lps4 ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
  destruct (fz_G al_rom r4 m4 s Hs80 Hs264 ltac:(csr; reflexivity)) as (r5 & RUN5 & G1 & G10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |]. clear RUN5.
  apply (pixDestroy_keep_W C A4 m4 (with_vmmaps vm4 md0) r5 (s - 80) (s - 48) pixs cm (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cm datas) cv (Z_to_bv 64 0x15770) S CK HW4
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           G1 ltac:(rok) ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) G10 R48' PX4 eq_refl eq_refl eq_refl Lps4 ltac:(rewrite HA0; exact (S0 _ (or_introl eq_refl)))
           Lds4 ltac:(rewrite HA0; exact (S0 _ (or_intror (or_introl eq_refl)))) Rpos NEsd).
  { cbn [p_data hdv]. destruct (box_e _ HCM) as [Z0 | (CM & CMOK & Lc & La & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
    pose proof CM as (Hc0 & Hc64 & _).
    destruct (blk_range C A3 m3 _ (Z_to_bv 64 cm) 24 CK HW3 Lc ltac:(lia)) as [Gc _]. rewrite u_Z2bv in Gc by lia. assert (NZ : cm <> 0%Z) by lia.
    assert (Bc1 : pblk pixs datas cm (c_arr cv) (Z_to_bv 64 cm)) by (right; right; split; [exact NZ | left; reflexivity]).
    assert (Bc2 : pblk pixs datas cm (c_arr cv) (Z_to_bv 64 (c_arr cv))) by (right; right; split; [exact NZ | right; reflexivity]).
    assert (Lc4 : live A4 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LS4 _ Bc1); exact Lc).
    split; [apply (CMAPat_frame mk); [exact (CMk NZ) | intros x Hx; exact (LIVK_at A4 mk m4 cm 24 x (proj2 PM4) Lc4 ltac:(lia) ltac:(lia) Hx)]|].
    split; [exact Lc4|]. split; [rewrite (LS4 _ Bc2); exact La|].
    split; [rewrite HA0; exact (S0 _ Bc1)|]. split; [rewrite HA0; exact (S0 _ Bc2)|].
    do 5 (split; [assumption|]).
    pose proof CMOK as (Hcd & Hna & _). rewrite Hna. destruct Hcd as [->|[->|[->| ->]]]; cbn; lia. }
  intros A5 m5 vm5 r6 HW5 CS6 PD5 PM5 R0 OUT5 RT5. rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RT5.
  replace (Z_to_bv 64 0x15770) with (0x15770 : word) by (apply bv_eq; reflexivity).
  replace (s - 48 + 8)%Z with (s - 40)%Z in PM5 by lia.
  cbn [p_data hdv] in PD5. destruct PD5 as (D1 & D2 & D3 & D4).
  pose proof (RT5 k b Hrm4 ltac:(lia) ltac:(lia)) as Hrm5. rewrite !Z.sub_0_r in Hrm5.
  assert (CE5 : cellsZ m5 (frameZ s ret regs)) by (apply (cellsF_frm C (s - 40) m4 m5 s ret regs CK (proj1 PM5)); [lia | lia | lia | lia | exact CE4]).
  assert (R56'' : rdn SEGS m5 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela)) by (apply (cell_out m4 m5); [intros x Hx; apply OUT5; lia | lia | lia | exact R56']).
  assert (LA5 : forall p, sela_blk sela arr 10 sels vs p -> live A5 (Z_to_bv 64 p) = live A4 (Z_to_bv 64 p)).
  { intros p Bp. pose proof (D_as p Bp) as NB. apply D4.
    - intros E. apply NB. left. exact E.
    - intros _ E. apply NB. right; left. exact E.
    - intros NZ. split; intros E; apply NB; right; right; (split; [exact NZ|]); [left | right]; exact E. }
  assert (SHM5 : sela_hm (alloc_top (c_vm C)) A5 m5 sela arr sels vs).
  { apply (sela_hm_keep_blk _ A4 A5 A5 m4 m5); [lia | exact SHM4 | exact LA5 | exact LA5 | exact (proj2 PM5)]. }
  (* [comment removed for export] *)
  destruct (fz_H al_rom r6 m5 s Hs80 Hs264 ltac:(csr; reflexivity)) as (r7 & RUN7 & J1 & J10 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |]. clear RUN7.
  replace (0x26eac : word) with (Z_to_bv 64 PC_selaDestroy) by (apply bv_eq; reflexivity).
  apply (SDES C A5 m5 (with_vmmaps vm5 md0) r7 (s - 80)%Z (s - 56)%Z sela arr sels vs (Z_to_bv 64 0x15778) S CK HW5
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold SELADESTROY_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) J1 ltac:(rok) ltac:(csr; reflexivity) J10 R56'' SHM5 ltac:(rewrite HA0; exact SOFF0)).
  intros A6 m6 vm6 r8 HW6 CS8 SOFF6 SONLY6 PM6 R0' OUT6 RT6. rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RT6.
  replace (Z_to_bv 64 0x15778) with (0x15778 : word) by (apply bv_eq; reflexivity).
  replace (s - 56 + 8)%Z with (s - 48)%Z in PM6 by lia.
  pose proof (RT6 k b Hrm5 ltac:(lia) ltac:(lia)) as Hrm6. rewrite !Z.sub_0_r in Hrm6.
  assert (CE6 : cellsZ m6 (frameZ s ret regs)) by (apply (cellsF_frm C (s - 48) m5 m6 s ret regs CK (proj1 PM6)); [lia | lia | lia | lia | exact CE5]).
  (* [comment removed for export] *)
  destruct (fz_Z al_rom r8 regs m6 s ret Hs80 Hs264 Hret CE6 ltac:(csr; reflexivity)) as (r9 & RUN9 & V2 & V1 & V10 & VR & AG9).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN9 |]. clear RUN9.
  apply (KF A6 m6 vm6 r9 k b HW6).
  - apply (live_back A A1 A2 A3 A4 A5 A6 (pblk pixs datas cm (c_arr cv)) Ba (oblk copy data cd ad)).
    + intros q. apply pblk_dec.
    + intros q. apply sela_blk_dec.
    + intros q. apply oblk_dec.
    + exact S0.
    + exact SE.
    + exact (Ba_off A SOFF0).
    + exact (Ba_only A1 A2 SONLY).
    + exact (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc).
    + exact CE3.
    + exact DEAD4.
    + intros q NB. rewrite (LEQ4 q NB). apply LQk.
    + intros q [E | [E | [NZ [E | E]]]]; subst q; [exact D1 | apply D2; lia | exact (proj1 (D3 NZ)) | exact (proj2 (D3 NZ))].
    + intros q NB. apply D4.
      * intros E. apply NB. left. exact E.
      * intros _ E. apply NB. right; left. exact E.
      * intros NZ. split; intros E; apply NB; right; right; (split; [exact NZ|]); [left | right]; exact E.
    + exact (Ba_off A6 SOFF6).
    + exact (Ba_only A5 A6 SONLY6).
  - exact V10.
  - apply cs_kept_intro; first [solve [apply VR; in_lit] | (csr; reflexivity)].
  - exact Hrm6.
  - exact Hk.
  - exact Hb.
Qed.

Lemma rounds : forall n : nat, (n <= 10)%nat -> forall i, i = (10 - Z.of_nat n)%Z -> (i < 10)%Z -> rinv i.
Proof.
  induction n as [|n IH]; intros Hn i Ei Hi; [lia|].
  apply (round_W i ltac:(lia)).
  - intros LT. exact (IH ltac:(lia) (i + 1)%Z ltac:(lia) LT).
  - intros _. exact PHX.
Qed.

(* [comment removed for export] *)
Lemma LOOP0 : forall r k3 b3, aroom A3 vm3 k3 b3 -> (kF + 120 <= k3)%Z -> (bF + 10 * RB10_hmt d w h <= b3)%Z ->
  getr r 2 = Z_to_bv 64 (s - 80) -> getr r 8 = Z_to_bv 64 sela -> getr r 9 = Z_to_bv 64 10 -> getr r 18 = Z_to_bv 64 copy ->
  getr r 19 = Z_to_bv 64 0 -> (forall x, In x DRz -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x1572c : word) m3 al_rom) (with_vmmaps vm3 md0)) S.
Proof.
  intros r k3 b3 Hrm3 Hk3 Hb3 Q2 Q8 Q9 Q18 Q19 RR.
  exact (rounds 10 ltac:(lia) 0%Z ltac:(lia) ltac:(lia) A3 m3 vm3 r k3 b3 (W_rebase C A3 m3 _ HW3) Hrm3 ltac:(lia) ltac:(lia) (FRM_refl _ _ _) (fun q => eq_refl)
           Q2 Q8 Q9 Q18 Q19 RR).
Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pre.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Hypothesis HMT : pixHMTDwa_1_contract.
Hypothesis SHMC : selaAddHitMiss_contract.
Hypothesis SDES : selaDestroy_contract.
Hypothesis GCNT : selaGetCount_run.
Hypothesis GSEL : selaGetSel_run.
Hypothesis GNAME : selGetName_run.

Variables (C : lctx) (A A1 : AS) (m2 : word -> option byte) (md0 : Model) (vm1 : VmMaps).
Variables (s : Z) (ret : word) (regs : bvmap 5 word) (S : TSet).
Variables (pixs w h d cm datas : Z) (cv : cmapv).
Variables (kF bF : Z).

Hypothesis CK : Cok C.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Htop : c_top C = s.
Hypothesis HA0 : c_A0 C = A.
Hypothesis Hret : ret_ok ret.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x45480.
Hypothesis HW2 : W C A1 m2 (with_vmmaps vm1 md0).
Hypothesis PXs : PIXat m2 pixs (hdv w h d cm datas).
Hypothesis HOK : hdr_ok w h d.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Lps : live A1 (Z_to_bv 64 pixs) = Some 64%Z.
Hypothesis Lds : live A1 (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z.
Hypothesis L0ps : live A (Z_to_bv 64 pixs) = None.
Hypothesis L0ds : live A (Z_to_bv 64 datas) = None.
Hypothesis NEsd : datas <> pixs.
Hypothesis HCM : boxed (cm = 0%Z \/ ((1 <= cm)%Z /\ CMAPat m2 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
                  cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ datas <> cm /\ datas <> c_arr cv)).
Hypothesis LEQ1 : forall q, q <> Z_to_bv 64 pixs -> q <> Z_to_bv 64 datas -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live A1 q = live A q.
Hypothesis CEZ : cellsZ m2 (frameZ s ret regs).
Hypothesis R48 : rdn SEGS m2 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs).
Hypothesis HkF : (0 <= kF)%Z.
Hypothesis HbF : (0 <= bF)%Z.
Hypothesis KF : forall A' m' vm' r' k' b', W C A' m' (with_vmmaps vm' md0) -> (forall q, live A' q = live A q) ->
    getr r' 10 = Z_to_bv 64 0 -> cs_kept regs r' -> aroom A' vm' k' b' -> (kF <= k')%Z -> (bF <= b')%Z ->
    realizes SEGS (mkCfg (mkst r' ret m' al_rom) (with_vmmaps vm' md0)) S.

(* [comment removed for export] *)
Lemma S0 : forall q, pblk pixs datas cm (c_arr cv) q -> live A q = None.
Proof.
  intros q [E | [E | [NZ B]]]; [subst q; exact L0ps | subst q; exact L0ds |].
  destruct (box_e _ HCM) as [Z0 | (_ & _ & _ & _ & _ & L0c & L0a & _)]; [contradiction|]. destruct B as [E | E]; subst q; assumption.
Qed.
Lemma S1 : forall q, pblk pixs datas cm (c_arr cv) q -> exists n, live A1 q = Some n.
Proof.
  intros q [E | [E | [NZ B]]]; [subst q; eexists; exact Lps | subst q; eexists; exact Lds |].
  destruct (box_e _ HCM) as [Z0 | (_ & _ & _ & Lc & La & _)]; [contradiction|]. destruct B as [E | E]; subst q; eexists; eassumption.
Qed.
Lemma SE : forall q, ~ pblk pixs datas cm (c_arr cv) q -> live A1 q = live A q.
Proof.
  intros q NB. apply LEQ1.
  - intros E. apply NB. left. exact E.
  - intros E. apply NB. right; left. exact E.
  - intros NZ. split; intros E; apply NB; right; right; (split; [exact NZ|]); [left | right]; exact E.
Qed.

(* [comment removed for export] *)
Definition sfacts (Ax : AS) (mx : word -> option byte) : Prop :=
  PIXat mx pixs (hdv w h d cm datas) /\ live Ax (Z_to_bv 64 pixs) = Some 64%Z /\ live Ax (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z /\
  (cm = 0%Z \/ ((1 <= cm)%Z /\ CMAPat mx cm cv /\ live Ax (Z_to_bv 64 cm) = Some 24%Z /\ live Ax (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).

Lemma sfacts_keep : forall Ax Ay Az mx my, sfacts Ax mx ->
  (forall q, pblk pixs datas cm (c_arr cv) q -> live Ay q = live Ax q) -> (forall q, pblk pixs datas cm (c_arr cv) q -> live Az q = live Ax q) ->
  LIVK Az mx my -> sfacts Ay my.
Proof.
  intros Ax Ay Az mx my (PX & Lp & Ld & HC) EQy EQz LK.
  pose proof PX as (Hp0 & Hp64 & _).
  assert (Lpz : live Az (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite EQz by (left; reflexivity); exact Lp).
  split; [apply (PIXat_frame mx); [exact PX | intros x Hx; exact (LIVK_at Az mx my pixs 64 x LK Lpz ltac:(lia) ltac:(lia) Hx)]|].
  split; [rewrite EQy by (left; reflexivity); exact Lp|].
  split; [rewrite EQy by (right; left; reflexivity); exact Ld|].
  destruct HC as [Z0 | (H1c & CM & Lc & La)]; [left; exact Z0 | right].
  pose proof CM as (Hc0 & Hc64 & _). assert (NZ : cm <> 0%Z) by lia.
  assert (Lcz : live Az (Z_to_bv 64 cm) = Some 24%Z) by (rewrite EQz by (right; right; split; [exact NZ | left; reflexivity]); exact Lc).
  split; [exact H1c|].
  split; [apply (CMAPat_frame mx); [exact CM | intros x Hx; exact (LIVK_at Az mx my cm 24 x LK Lcz ltac:(lia) ltac:(lia) Hx)]|].
  split; [rewrite EQy by (right; right; split; [exact NZ | left; reflexivity]); exact Lc | rewrite EQy by (right; right; split; [exact NZ | right; reflexivity]); exact La].
Qed.

Lemma PH0 : forall r k1 b1, aroom A1 vm1 k1 b1 ->
  (kF + RK10_sela + RK_pixcopy + 120 <= k1)%Z -> (bF + RB10_sela + RB_pixcopy14 + 10 * RB10_hmt d w h <= b1)%Z ->
  getr r 2 = Z_to_bv 64 (s - 80) -> getr r 1 = Z_to_bv 64 0x15700 -> getr r 10 = Z_to_bv 64 0 -> getr r 18 = Z_to_bv 64 pixs ->
  (forall x, In x DRz -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x27be8 : word) m2 al_rom) (with_vmmaps vm1 md0)) S.
Proof.
  intros r k1 b1 Hrm1 Hk1 Hb1 Q2 Q1 Q10 Q18 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. rewrite Htop in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs80 : (80 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  pose proof (RBpos w h d HOK) as HBpos.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z /\ (0 <= RK10_sela)%Z /\ (0 <= RB10_sela)%Z) by (clear; room_consts; lia).
  destruct KP as (KP1 & KP2 & KP3 & KP4).
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  assert (Rpos : (0 < 4 * (wpl_of w d * h))%Z) by (assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (SF1 : sfacts A1 m2).
  { split; [exact PXs|]. split; [exact Lps|]. split; [exact Lds|].
    destruct (box_e _ HCM) as [Z0 | (H1c & CM & _ & Lc & La & _)]; [left; exact Z0 | right; split; [exact H1c | split; [exact CM | split; [exact Lc | exact La]]]]. }
  (* [comment removed for export] *)
  replace (0x27be8 : word) with (Z_to_bv 64 PC_selaAddHitMiss) by (apply bv_eq; reflexivity).
  pose proof Hrm1 as Hrm1'. rewrite <- (with_vmmaps_vmmaps vm1 md0) in Hrm1'.
  apply (SHMC C A1 m2 (with_vmmaps vm1 md0) r (s - 80)%Z (Z_to_bv 64 0x15700) S CK HW2 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold SELAHM_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Q1 ltac:(rok) ltac:(rewrite (RR 4%bv) by in_lit; exact H4) Q10
           k1 b1 Hrm1' ltac:(lia) ltac:(lia)).
  intros A2 m' vm2 r1 sela arr sels vs HW' CS1 PM' A10 SHM2 SOFF1 SOFF0 SONLY Hrm2. rewrite with_vmmaps_twice in HW' |- *.
  replace (Z_to_bv 64 0x15700) with (0x15700 : word) by (apply bv_eq; reflexivity).
  rewrite HA0 in SOFF0.
  assert (NSB : forall p q, sela_blk sela arr 10 sels vs p -> pblk pixs datas cm (c_arr cv) q -> q <> Z_to_bv 64 p).
  { intros p q Bp Bq E. subst q. destruct (S1 _ Bq) as [n Ln]. rewrite (SOFF1 p Bp) in Ln. discriminate. }
  assert (LS2 : forall q, pblk pixs datas cm (c_arr cv) q -> live A2 q = live A1 q) by (intros q Bq; apply SONLY; intros p Bp; exact (NSB p q Bp Bq)).
  pose proof (sfacts_keep A1 A2 A1 m2 m' SF1 LS2 (fun _ _ => eq_refl) (proj2 PM')) as SF2.
  assert (SLIV2 : forall p, sela_blk sela arr 10 sels vs p -> exists n, live A2 (Z_to_bv 64 p) = Some n).
  { intros p Bp. destruct (sela_blk_live_all _ _ _ _ _ _ _ _ _ p (proj1 SHM2) Bp) as (n & Ln & _). exists n. exact Ln. }
  assert (CE2 : cellsZ m' (frameZ s ret regs)) by (apply (cellsF_frm C (s - 80) m2 m' s ret regs CK (proj1 PM')); [lia | lia | lia | lia | exact CEZ]).
  assert (R48' : rdn SEGS m' (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs)) by (apply (cell_frm C (s - 80) m2 m'); [exact CK | exact (proj1 PM') | lia | lia | lia | exact R48]).
  pose proof (proj1 SHM2) as (_ & Bs & _). pose proof Bs as (Gs & Ts & ALs).
  (* [comment removed for export] *)
  destruct (fz_C al_rom r1 m' s sela Hs80 Hs264 (W_sok_win C A2 m' _ (s - 56) 8 CK HW' ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) A10) as (r2 & RUN2 & E1 & E10 & E8 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
  set (M3 := wbytes m' (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 sela))).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md0) /\ POSTM C A2 s m' M3) by (subst M3; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M3 x = m' x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (sfacts_keep A2 A2 A2 m' M3 SF2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM3)) as SF3.
  assert (SHM3 : sela_hm (alloc_top (c_vm C)) A2 M3 sela arr sels vs) by (apply (sela_hm_keep _ A2 A2 m' M3); [lia | exact SHM2 | apply sub_live_refl | exact (proj2 PM3)]).
  assert (CE3 : cellsZ M3 (frameZ s ret regs)) by (apply (cellsF_out m' M3 (s - 56) (s - 48) s ret regs OUT3); [lia | lia | lia | exact CE2]).
  assert (R48'' : rdn SEGS M3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs)) by (apply (cell_out m' M3); [intros x Hx; apply OUT3; lia | lia | lia | exact R48']).
  assert (R56 : rdn SEGS M3 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela)) by (subst M3; apply cell_wr; lia).
  pose proof (proj1 SHM3) as (_ & _ & _ & Rs3 & _).
  replace (0x27aa0 : word) with (Z_to_bv 64 PC_selaGetCount) by (apply bv_eq; reflexivity).
  destruct (GCNT al_rom r2 M3 sela 10%Z 50%Z arr (Z_to_bv 64 0x1570c) Rs3 ltac:(lia) (bok_mod8 _ _ _ Bs) ltac:(lia) E1 ltac:(rok) E10) as (r3 & RUN3 & N10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN3 |]. clear RUN3.
  replace (Z_to_bv 64 0x1570c) with (0x1570c : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  destruct (fz_D al_rom r3 M3 10 pixs N10 ltac:(csr; reflexivity)) as (r4 & RUN4 & F1 & F10 & F11 & F9 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
  pose proof SF3 as (PX3 & Lp3 & Ld3 & HC3).
  pose proof Hrm2 as Hrm2'. rewrite <- (with_vmmaps_vmmaps vm2 md0) in Hrm2'.
  refine (pixCopy_W C A2 M3 (with_vmmaps vm2 md0) r4 (s - 80) pixs w h d cm datas cv (Z_to_bv 64 0x1571c) S CK HW3 ltac:(csr; reflexivity)
            ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) F1 ltac:(rok) ltac:(csr; reflexivity) F10 F11
            PX3 HOK Hw Hh Lp3 Ld3 _ (k1 - RK10_sela)%Z (b1 - RB10_sela)%Z Hrm2' ltac:(lia) ltac:(lia) _).
  { destruct HC3 as [Z0 | (H1c & CM & Lc & La)]; [left; exact Z0 | right]. destruct (box_e _ HCM) as [Z0 | (_ & _ & CMOK & _)]; [lia|].
    split; [exact CM | split; [exact CMOK | split; [exact Lc | exact La]]]. }
  unfold TK. intros A3 m'' vm3 r5 HW'' CS5 PM'' RES Hrm3. rewrite with_vmmaps_twice in HW'' |- *.
  replace (Z_to_bv 64 0x1571c) with (0x1571c : word) by (apply bv_eq; reflexivity).
  destruct (res_oown_d C A2 A3 m'' r5 w h d cv Rpos RES) as (copy & cd & data & ad & R10 & OOc & CE3').
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc CE3') as SUB3.
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc) as Hcp.
  assert (LS3 : forall q, pblk pixs datas cm (c_arr cv) q -> live A3 q = live A2 q).
  { intros q Bq. apply CE3'. intros B. destruct (S1 _ Bq) as [n Ln]. rewrite <- (LS2 q Bq) in Ln.
    rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OOc q B) in Ln. discriminate. }
  pose proof (sfacts_keep A2 A3 A2 M3 m'' SF3 LS3 (fun _ _ => eq_refl) (proj2 PM'')) as SF4.
  assert (SHM4 : sela_hm (alloc_top (c_vm C)) A3 m'' sela arr sels vs) by (apply (sela_hm_keep _ A2 A3 M3 m''); [lia | exact SHM3 | exact SUB3 | exact (proj2 PM'')]).
  assert (CE4 : cellsZ m'' (frameZ s ret regs)) by (apply (cellsF_frm C (s - 80) M3 m'' s ret regs CK (proj1 PM'')); [lia | lia | lia | lia | exact CE3]).
  assert (R48_4 : rdn SEGS m'' (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs)) by (apply (cell_frm C (s - 80) M3 m''); [exact CK | exact (proj1 PM'') | lia | lia | lia | exact R48'']).
  assert (R56_4 : rdn SEGS m'' (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela)) by (apply (cell_frm C (s - 80) M3 m''); [exact CK | exact (proj1 PM'') | lia | lia | lia | exact R56]).
  (* [comment removed for export] *)
  destruct (fz_E al_rom r5 m'' s copy Hs80 Hs264 (W_sok_win C A3 m'' _ (s - 64) 8 CK HW'' ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) R10 ltac:(csr; reflexivity))
    as (r6 & RUN6 & V18 & V19 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN6 |]. clear RUN6.
  set (M4 := wbytes m'' (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 copy))).
  assert (WP4 : W C A3 M4 (with_vmmaps vm3 md0) /\ POSTM C A3 s m'' M4) by (subst M4; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M4 x = m'' x).
  { intros x Hx. subst M4. apply (wbytes_out_Z _ (s - 64) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  pose proof (sfacts_keep A3 A3 A3 m'' M4 SF4 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)) as (PX5 & Lp5 & Ld5 & HC5).
  assert (SHM5 : sela_hm (alloc_top (c_vm C)) A3 M4 sela arr sels vs) by (apply (sela_hm_keep _ A3 A3 m'' M4); [lia | exact SHM4 | apply sub_live_refl | exact (proj2 PM4)]).
  pose proof (oown_keep C A2 A3 A3 A3 m'' M4 _ _ _ _ _ _ _ _ _ _ OOc (fun _ _ => eq_refl) (fun _ _ => eq_refl) (proj2 PM4)) as OOc5.
  assert (CE5 : cellsZ M4 (frameZ s ret regs)) by (apply (cellsF_out m'' M4 (s - 64) (s - 56) s ret regs OUT4); [lia | lia | lia | exact CE4]).
  assert (R48_5 : rdn SEGS M4 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixs)) by (apply (cell_out m'' M4); [intros x Hx; apply OUT4; lia | lia | lia | exact R48_4]).
  assert (R56_5 : rdn SEGS M4 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 sela)) by (apply (cell_out m'' M4); [intros x Hx; apply OUT4; lia | lia | lia | exact R56_4]).
  assert (R64_5 : rdn SEGS M4 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 copy)) by (subst M4; apply cell_wr; lia).
  assert (HCM5 : boxed (cm = 0%Z \/ (CMAPat M4 cm cv /\ cmap_ok cv /\ live A3 (Z_to_bv 64 cm) = Some 24%Z /\ live A3 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                  cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ datas <> cm /\ datas <> c_arr cv))).
  { apply box_i. destruct HC5 as [Z0 | (H1c & CM & Lc & La)]; [left; exact Z0 | right].
    destruct (box_e _ HCM) as [Z0 | (_ & _ & CMOK & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5)]; [lia|]. repeat (split; [assumption|]). exact N5. }
  apply (LOOP0 HMT SDES GSEL GNAME C A A1 A2 A3 M4 md0 vm3 s ret regs S pixs w h d cm datas cv sela arr sels vs copy cd data ad kF bF
           CK Hs16 Htop HA0 Hret H2 H4 HW4 PX5 HOK Hw Hh Lp5 Ld5 NEsd HCM5 S0 S1 SE SHM5 SOFF0 SOFF1 SLIV2 SONLY OOc5 CE3' CE5 R48_5 R56_5 R64_5 HkF HbF KF
           r6 (k1 - RK10_sela - RK_pixcopy)%Z (b1 - RB10_sela - RB_pixcopy14)%Z Hrm3 ltac:(lia) ltac:(lia)).
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - exact V18.
  - exact V19.
  - drz_solve.
Qed.

End Pre.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_fhmtgen <= FUZZ_CALLS)%Z /\
  (forall size d w h, (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z -> (RB_fhmtgen d w h <= fuzz_margin size)%Z).
Proof. split; [rewrite RK_fhmtgen_val; unfold FUZZ_CALLS; lia | intros size d w h Hw Hh; unfold fuzz_margin; exact (RB_fhmtgen_le d w h Hw Hh)]. Qed.

Theorem lept_fuzz_call :
  (forall fx : FPState, @pixHMTDwa_1_contract fx AL CL ASR) -> (forall fx : FPState, @selaAddHitMiss_contract fx AL CL ASR) ->
  (forall fx : FPState, @selaDestroy_contract fx AL CL ASR) ->
  (forall fx : FPState, @selaGetCount_run fx) -> (forall fx : FPState, @selaGetSel_run fx) -> (forall fx : FPState, @selGetName_run fx) ->
  @fuzz_call_contract AL CL ASR.
Proof.
  intros HMT0 SHMC0 SDES0 GCNT0 GSEL0 GNAME0. unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret H3 H4 Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot Hsel kR bR Hrm Hrk Hrb K.
  pose proof (HMT0 fx) as HMT. pose proof (SHMC0 fx) as SHMC. pose proof (SDES0 fx) as SDES. pose proof (GCNT0 fx) as GCNT. pose proof (GSEL0 fx) as GSEL. pose proof (GNAME0 fx) as GNAME.
  clear HMT0 SHMC0 SDES0 GCNT0 GSEL0 GNAME0.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in H4.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, V10Drv1.V10FuzzIface.A_SELNAMES, SELNAMES_LEN, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x156ac) with (0x156ac : word) by (apply bv_eq; reflexivity).
  pose proof (u64_range (getr regs 2)) as Hs. pose proof (u64_range dptr) as Hdp. pose proof (u64_range sp0) as Hsp0r.
  set (s := u (getr regs 2)) in *.
  assert (H2 : getr regs 2 = Z_to_bv 64 s) by (subst s; rewrite zbv_self; reflexivity). clearbody s.
  set (dp := u dptr) in *.
  assert (Edp : dptr = Z_to_bv 64 dp) by (subst dp; rewrite zbv_self; reflexivity). clearbody dp. rewrite Edp in Ha0, Hlive, Hempty.
  set (C := LCTX sp0 argv envp s (m_vmmaps md) m A).
  assert (Etop : c_top C = s) by reflexivity. assert (Evm : c_vm C = m_vmmaps md) by reflexivity.
  assert (CK : Cok C) by (constructor; cbn; rewrite ?LSTK_val; lia).
  pose proof LSTK_val as LV.
  assert (Hs80 : (80 <= s)%Z) by lia. assert (Hs264 : (s < 2 ^ 64)%Z) by lia.
  (* [comment removed for export] *)
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT5 : forall a : word, ~ (s - 40 <= u a < s)%Z -> FZ5 m s ret regs a = m a) by (intros a Ha; apply FZ5_out; lia).
  assert (GR5 : mem_grows m (FZ5 m s ret regs)) by (unfold FZ5; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom regs m s size (Z_to_bv 64 dp) ret Hs80 Hs264 ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & QR & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K A (FZ5 m s ret regs) (m_vmmaps md) r1).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT5. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR5 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 40)); [rewrite OUT5 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT5 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - apply cs_kept_intro; first [solve [apply QR; in_lit] | (csr; reflexivity)].
    - intros a _ _ _ _ NW. apply OUT5. lia.
    - intros q k i L Hi. apply OUT5. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR5 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - apply (aroom_mono A (m_vmmaps md) kR bR); [exact Hrm | lia | lia]. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x34e08) 8 = true) by exact Hhdl.
  destruct (fz_A al_rom regs m s size (Z_to_bv 64 dp) ret Hs80 Hs264 ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FZ5 m s ret regs) (Z_to_bv 64 0x34e08) (word_to_le_bytes 8 (Z_to_bv 64 0x15798))) in *.
  assert (OUT1 : forall a : word, ~ (s - 40 <= u a < s)%Z -> ~ (0x34e08 <= u a < 0x34e10)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT5; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR5 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LLU16] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc.
      destruct Hc as [Hc|[Hc|[Hc|[Hc|[]]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia | apply Hsel; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 40)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x34e08); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0x34e10); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LLU16]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (CE1 : cellsZ m1 (frameZ s ret regs)).
  { apply (cellsF_out (FZ5 m s ret regs) m1 0x34e08 0x34e10 s ret regs); [| lia | lia | lia | exact (cells_FZ5 m s ret regs Hs80 Hs264)].
    intros x Hx. subst m1. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KF : forall A' mf vm' rr k' b', W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> aroom A' vm' k' b' -> (kR - FUZZ_CALLS <= k')%Z -> (bR - fuzz_margin size <= b')%Z ->
               realizes SEGS (mkCfg (mkst rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros A' mf vm' rr k' b' HWf LQ A0 CS HRf Hk' Hb'. apply (K A' mf vm' rr).
    - pose proof (w_inv _ _ _ _ HWf) as X. rewrite with_vmmaps_vmmaps in X. exact X.
    - exact LQ.
    - exact A0.
    - exact CS.
    - intros a N1 N2 N3 N4 N5. apply (w_frm _ _ _ _ HWf a); [exact N1 | exact N2 | exact N3 | unfold hcell; cbn; exact N4 | unfold scratch; cbn; rewrite LV; lia].
    - intros q k i Lq Hi. exact (w_live0 _ _ _ _ HWf q k i Lq Hi).
    - intros a Hx. exact (w_def _ _ _ _ HWf a Hx).
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V1. exact V1.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V2. exact V2.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V3. exact V3.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V4. exact V4.
    - apply (aroom_mono A' vm' k' b'); [exact HRf | lia | lia]. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4%bv) by notin_list; exact H4).
  assert (RKD : (RK_deser <= kR)%Z /\ (RB_deser <= bR)%Z).
  { pose proof (FZb size 1%Z 1%Z 1%Z ltac:(lia) ltac:(lia)) as X. pose proof (proj1 (RB10_hmt_le 1 1 1 ltac:(lia) ltac:(lia))) as Y.
    unfold RB_fhmtgen in X. rewrite RK_fhmtgen_val in FZk. clear - X Y FZk Hrk Hrb. room_consts. lia. }
  apply (pixDeserialize_W C A m1 md r1 (s - 80) dp pl (Z_to_bv 64 0x156ec) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(rok) Q4 Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia) ltac:(apply al16_mod4; exact Hal16)
           kR bR Hrm (proj1 RKD) (proj2 RKD)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x156ec) with (0x156ec : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (CE' : cellsZ m' (frameZ s ret regs)) by (apply (cellsF_frm C (s - 80) m1 m' s ret regs CK F'); [rewrite Etop, LV; lia | lia | lia | lia | exact CE1]).
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 80)) by (csr; reflexivity).
  pose proof (W_sok_win C A' m' _ (s - 48) 8 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO & PF)].
  - (* [comment removed for export] *)
    destruct (fz_B0 al_rom r2 regs m' s ret Hs80 Hs264 Hret SOK' CE' Y2 A0) as (r3 & RUN3 & V2 & V1 & V10 & VR & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    assert (HWf : W C A' (wbytes m' (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md)).
    { apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    apply (KF A' _ vm' r3 _ _ HWf LQ V10 ltac:(apply cs_kept_intro; first [solve [apply VR; in_lit] | (csr; reflexivity)]) Hrm').
    + destruct RKD. rewrite RK_fhmtgen_val in FZk. clear - FZk. room_consts. lia.
    + pose proof (FZb size 1%Z 1%Z 1%Z ltac:(lia) ltac:(lia)) as X. pose proof (proj1 (RB10_hmt_le 1 1 1 ltac:(lia) ltac:(lia))) as Y.
      unfold RB_fhmtgen in X. clear - X Y. room_consts. lia.
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
    pose proof PF as (Ev & HOK & Hw & Hh & CMOK).
    destruct v as [w h d spp wpl rc xres yres fmt spec text cm datas].
    cbn [p_w p_h p_d p_spp p_wpl p_rc p_xres p_yres p_fmt p_spec p_text p_cmap p_data] in PX, Rrc, Rtx, Hn4, Ld, LdA, Ld0, NEdp, RC, RQ, Ev, HOK, Hw, Hh, CMOK.
    injection Ev as E8 E7 E6 E5 E4 E3 E2 E1. subst spp wpl rc xres yres fmt spec text.
    change (PIXV w h d (spp_of d) (wpl_of w d) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z cm datas) with (hdv w h d cm datas) in PX.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
    pose proof (alloc_top_lt (m_vmmaps md)) as ATL. unfold two_pow_64 in ATL.
    destruct (fz_B1 al_rom r2 m' s pix Hs80 Hs264 ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V1 & V10 & V18 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (m2 := wbytes m' (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    assert (HW2 : W C A' m2 (with_vmmaps vm' md)).
    { subst m2. apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    assert (OUT2 : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> m2 x = m' x).
    { intros x Hx. subst m2. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PX2 : PIXat m2 pix (hdv w h d cm datas)) by (apply (PIXat_frame m'); [exact PX | intros x Hx; apply OUT2; lia]).
    assert (HCM : boxed (cm = 0%Z \/ ((1 <= cm)%Z /\ CMAPat m2 cm cv /\ cmap_ok cv /\ live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                    live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
                    cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ datas <> cm /\ datas <> c_arr cv))).
    { apply box_i. destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A' m' _ (Z_to_bv 64 cm) 24 CK HW' Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
      split; [exact Hc1|]. split; [apply (CMAPat_frame m'); [exact CM | intros x Hx; apply OUT2; lia] |]. split; [exact (CMOK ltac:(lia))|].
      repeat (split; [assumption|]). exact N5. }
    assert (CE2 : cellsZ m2 (frameZ s ret regs)) by (apply (cellsF_out m' m2 (s - 48) (s - 40) s ret regs OUT2); [lia | lia | lia | exact CE']).
    assert (R48 : rdn SEGS m2 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pix)) by (subst m2; apply cell_wr; lia).
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz4).
    pose proof (FZb size d w h ltac:(lia) ltac:(lia)) as FZb'.
    apply (PH0 HMT SHMC SDES GCNT GSEL GNAME C A A' m2 md vm' s ret regs S pix w h d cm datas cv (kR - FUZZ_CALLS)%Z (bR - fuzz_margin size)%Z
             CK Hsp16 Etop eq_refl Hret H2 H4 HW2 PX2 HOK Hw Hh Lp Ld LpA LdA NEdp HCM RQ CE2 R48 ltac:(lia) ltac:(lia) KF
             r3 (kR - RK_deser)%Z (bR - RB_deser)%Z Hrm').
    + rewrite RK_fhmtgen_val in FZk. clear - FZk Hrk. room_consts. lia.
    + unfold RB_fhmtgen in FZb'. clear - FZb' Hrb. lia.
    + csr; reflexivity.
    + exact V1.
    + exact V10.
    + exact V18.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [rewrite (AG3 _) by notin_list; rewrite (cs_kept_get _ _ _ CS') by (first [exact cs3 | exact cs4 | exact cs20 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27]); rewrite (AG1 _) by notin_list; reflexivity|]). destruct Hx.
Qed.
End Final.
End V10LeptFuzzMain.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10Kit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptRop.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptGrayBorderW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptDwa.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptSelHM.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10LeptSelDestroy.
Module V10LeptPinsI.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LeptDefs.
Import V10Kit.
Import V10Drv1.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
(* [comment removed for export] *)







Import V10Kit.V10MallocLayout.

Import V10Drv1.V10FuzzIface.





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rdn_agree_on : forall segs (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x : word, a <= u x < a + Z.of_nat n -> M' x = M x) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros segs M M' a n Ha Hn E. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply E. lia.
Qed.

#[export] Instance u16_lept_pins : @LeptPins (@mallocng_alloc_layout LU16) LLU16.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LLU16 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LU16]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU16] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x6570b 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x65738 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LU16] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU16] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU16] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LU16] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU16] in H. lia.
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

#[export] Instance u16_pins16 : @V10Pins (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem u16_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16),
  @fuzz_call_contract (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16) ASR.
Proof.
  intros ASR.
  apply (@V10LeptFuzzMain.lept_fuzz_call _ _ ASR u16_lept_pins u16_pins16); intros fx.
  - pose proof (@V10LeptRop.pixRasterop_uni_closed fx _ _ ASR u16_lept_pins u16_pins16) as ROPU. pose proof (@V10LeptRop.pixRasterop_src_W fx _ _ ASR u16_lept_pins u16_pins16) as ROPS.
    exact (@V10LeptHmtW.pixHMTDwa_1_W fx _ _ ASR u16_lept_pins u16_pins16
             (@V10LeptGrayBorderW.pixAddBorderGeneral_W fx _ _ ASR u16_lept_pins u16_pins16 ROPU ROPS) (@V10LeptGrayBorderW.pixRemoveBorderGeneral_W fx _ _ ASR u16_lept_pins u16_pins16 ROPS)
             (@V10LeptFhmtW.pixFHMTGen_1_W fx _ _ ASR u16_lept_pins u16_pins16 (@V10CL8a.V10LeptSelSegs.strcmp_run_W fx) (@V10LeptDwa.fhmtgen_low_1_W fx _ _ ASR u16_lept_pins u16_pins16))
             (@V10LeptFhmtW.pixFHMTGen_1_null_W fx _ _ ASR u16_lept_pins u16_pins16)).
  - exact (@V10LeptSelHM.selaAddHitMiss_W fx _ _ ASR u16_lept_pins u16_pins16).
  - exact (@V10LeptSelDestroy.selaDestroy_W fx _ _ ASR u16_lept_pins u16_pins16).
  - exact (@V10CL8a.V10LeptSelSegs.selaGetCount_run_W fx).
  - exact (@V10CL8a.V10LeptSelSegs.selaGetSel_run_W fx).
  - exact (@V10CL8a.V10LeptSelSegs.selGetName_run_W fx).
Qed.
End V10LeptPinsI.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefLayout.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10Main.
Module V10Pins.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import V10Kit.
Import V10Drv1.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V10Kit.V10MallocLayout. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts.

Import V10Drv1.V10MainEntry. Import V10Drv1.V10Open. Import V10Drv1.V10Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x6570b) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem u16_pins : @V10Main.pins (@mallocng_alloc_layout LU16).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU16] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LU16] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU16] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU16] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x453b0 <= a)%Z -> (a + Z.of_nat n <= 0x65778)%Z -> (a + Z.of_nat n <= 0x453dc \/ 0x453e0 <= a)%Z ->
              (a + Z.of_nat n <= 0x654c0 \/ 0x656e0 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x6570b) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x6570b%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x6570b%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x6570b) + Z.of_nat 0)%Z with 0x6570b%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x65738%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LU16]. change (bv_unsigned (Z_to_bv 64 0x65708) + 8)%Z with 0x65710%Z.
        rewrite (LIBC 0x65710%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x33dc0)) with 0x33dc0%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End V10Pins.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Spec.
Module V10Closed.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Spec.
Import V10Kit.
Import V10Pins.
Import V10Drv1.
Import V10LeptPinsI.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10.V10Main.
(* [comment removed for export] *)







Import V10Kit.V10MallocLayout. Import V10Kit.V10Alloc. Import V10Kit.V10Sure.


Import V10Drv1.V10FuzzIface.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem u16_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Ubsan.M.loaded_segments
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@V10Main.ref_realizes_spec_pins _ _ u16_sure V10Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
End V10Closed.
