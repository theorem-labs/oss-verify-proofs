(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF5s.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section ENQSPIN.
  Variables (mem rom : word -> option byte).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Rg1 : rdn BSEGS mem (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis Rg2 : rdn BSEGS mem (Z_to_bv 64 0x105f60) 8 = Some (LE8 (Z_to_bv 64 0x19fcdc)).
  Hypothesis Rdy : rdn BSEGS mem (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma enq_spin_run : exists r, msteps BSEGS (mkst regs (0x50c5c : word) mem rom) (mkst r (0x50c98 : word) mem rom).
  Proof using Rdy Rg2 Rg1 H10.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    wd_eexists.
    an F_50c5c D_50c5c.                                (* [comment removed for export] *)
    ab_tk F_50c60 D_50c60 ltac:(condz).                (* [comment removed for export] *)
    an F_50c7c D_50c7c.                                (* [comment removed for export] *)
    cld8 F_50c80 D_50c80 (Z_to_bv 64 1) Rg1.           (* [comment removed for export] *)
    ab_ft F_50c84 D_50c84 ltac:(condz).                (* [comment removed for export] *)
    an F_50c88 D_50c88.                                (* [comment removed for export] *)
    cld8 F_50c8c D_50c8c (Z_to_bv 64 0x19fcdc) Rg2.    (* [comment removed for export] *)
    clw F_50c90 D_50c90 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rdy V0.   (* [comment removed for export] *)
    try (rewrite (v_lw_small 0) by lia).
    ab_ft F_50c94 D_50c94 ltac:(condz).                (* [comment removed for export] *)
    wd_refl.
  Qed.
End ENQSPIN.

(* [comment removed for export] *)
Lemma enq_spin_to_spin : forall (r : bvmap 5 word) (M rom : word -> option byte) (model : Model),
  to_spin BSEGS (mkst r (0x50c98 : word) M rom) model.
Proof using.
  intros r M rom model.
  apply (ts_spin_of_step_j BSEGS (mkst r (0x50c98 : word) M rom) model W_50c98 0 0 4%Z);
    [reflexivity | exact F_50c98 | reflexivity | exact D_50c98 | reflexivity | reflexivity].
Qed.
End FPGen.
End BoAllocF5s.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFPutR1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR.BoAllocF5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR.BoAllocFRun3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR.BoAllocFRun3Rf OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR BoAllocF5s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8R1 : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sp_mod16_2272 : forall s, s mod 16 = 0 -> (s + -2272) mod 16 = 0.
Proof. intros s Hs. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PUTR1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.            (* [comment removed for export] *)
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition putR1_post (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K1 m : Z) (p : word)
             (st' : ast) (c' : config) : Prop :=
    let S := getr R 2 in
    exists fx'' (R'' : bvmap 5 word) (M'' M0'' : mem) (mdl'' : Model) (st'' : ast) (ks : list Z) (k : Z),
      c' = mkCfg (@mkst fx'' R'' (Z_to_bv 64 0x50c5c) M'' (seg_rom BSEGS)) mdl''
      /\ FXOK fx'' /\ m_halted mdl'' = None /\ BackingAlgebra.model_ivs_wf mdl''
      /\ WF bt st'' Lc FF /\ Rep bt st'' Lc FF M0'' mdl'' /\ bounds st'' Lc B C K1 /\ HPc h st''
      /\ a_cache st'' BATCHCLASS = ks ++ [k] /\ a_tq st'' = a_tq st' /\ a_gq st'' = a_gq st'
      /\ (forall a : word, M'' a <> M0'' a -> X2 (U S) (U p) T m (U a) /\ M'' a <> None)
      /\ (forall a : word, M'' a <> M a ->
            (X2 (U S) (U p) T m (U a) \/ (U S - 3584 <= U a < U S)
             \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
            /\ M'' a <> None)
      /\ M'' (at_ p (-16)) = Some (Z_to_bv 8 3)
      /\ (forall i, 0 <= i < up8 m / 8 -> M'' (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd))
      /\ (rdn BSEGS M'' (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)) /\ rdn BSEGS M'' (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728)))
          /\ rdn BSEGS M'' (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)) /\ rdn BSEGS M'' (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 m))
          /\ rdn BSEGS M'' (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))) /\ rdn BSEGS M'' (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208))
          /\ rdn BSEGS M'' (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16)))
          /\ rdn BSEGS M'' (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)) /\ rdn BSEGS M'' (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))))
      /\ (rdn BSEGS M'' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) /\ rdn BSEGS M'' (at_ S (-2144)) 8 = Some (LE8 S)
          /\ rdn BSEGS M'' (at_ S (-2152)) 8 = Some (LE8 p) /\ rdn BSEGS M'' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))
          /\ rdn BSEGS M'' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) /\ rdn BSEGS M'' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))
          /\ rdn BSEGS M'' (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))) /\ rdn BSEGS M'' (at_ S (-2192)) 8 = Some (LE8 (getr R 22)))
      /\ (rdn BSEGS M'' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) /\ rdn BSEGS M'' (at_ S (-16)) 8 = Some (LE8 (getr R 8))
          /\ rdn BSEGS M'' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) /\ rdn BSEGS M'' (at_ S (-32)) 8 = Some (LE8 (getr R 18))
          /\ rdn BSEGS M'' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) /\ rdn BSEGS M'' (at_ S (-48)) 8 = Some (LE8 (getr R 20))
          /\ rdn BSEGS M'' (at_ S (-56)) 8 = Some (LE8 (getr R 21)))
      /\ (getr R'' 10 = Z_to_bv 64 1 /\ getr R'' 2 = at_ S (-2272) /\ getr R'' 8 = at_ (Z_to_bv 64 T) 2128 /\ getr R'' 9 = at_ (Z_to_bv 64 T) 208
          /\ getr R'' 18 = at_ p (-16) /\ getr R'' 19 = at_ (Z_to_bv 64 T) 80 /\ getr R'' 21 = Z_to_bv 64 m /\ getr R'' 22 = Z_to_bv 64 (2 ^ 20)
          /\ getr R'' 3 = getr R 3 /\ getr R'' 4 = getr R 4
          /\ getr R'' 23 = getr R 23 /\ getr R'' 24 = getr R 24 /\ getr R'' 25 = getr R 25 /\ getr R'' 26 = getr R 26 /\ getr R'' 27 = getr R 27)
      /\ same_except_vm mdl mdl'' /\ lazy_kept (bt_ia bt) Lc FF mdl mdl''.

  (* [comment removed for export] *)
  Definition free_putR1_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z),
      let S := getr R 2 in
      (* [comment removed for export] *)
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      (* [comment removed for export] *)
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      (a_tq st' = [] \/ exists tq' b, a_tq st' = tq' ++ [b] /\ Z.of_nat (length (ba_items b)) = BATCHCAP) ->
      a_cache st' BATCHCLASS = [] -> m <= 2 ^ 28 -> K1 <= KCAP -> mu_room st' ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      rdn BSEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) -> rdn BSEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn BSEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn BSEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)) ->
      rdn BSEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn BSEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn BSEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn BSEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn BSEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn BSEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn BSEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn BSEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 2 = at_ S (-2176) -> getr R' 8 = at_ p (-16) -> getr R' 9 = at_ S (-2128) -> getr R' 10 = Z_to_bv 64 id ->
      getr R' 18 = Z_to_bv 64 (IB bt) -> getr R' 19 = Z_to_bv 64 0 -> getr R' 20 = Z_to_bv 64 T -> getr R' 21 = at_ S (-81) ->
      getr R' 22 = getr R 22 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      0 <= id < 2 ^ 32 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD BSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS)) mdl')
           (putR1_post h R M mdl Lc FF B C K1 m p st').

  Theorem free_putR1 : free_putR1_stmt.
  Proof using FAM HP CELLSPIN HYP_REFILL G_KR KR G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putR1_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id CP HR10 ELc W' RP' BD' HLE TQC ECA M28 KC1 MUR1
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    unfold IB in Y18. rewrite BT_ia in Y18. cbn [ia_instance both_addrs] in Y18.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & _ & _ & _ & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_batch_geom_stmt in OBL_batch_geom.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    clear AB3 GCT' GCB.
    clear OBL_blk_geom.
    assert (T16 : T mod 16 = 0) by (clear -TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof R17 as Csb.
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    destruct (TPC BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (PCcnt & _ & _ & _). rewrite ECA in PCcnt. cbn [length Z.of_nat] in PCcnt.
    unfold T_PC, PC_SZ, BATCHCLASS in PCcnt.
    destruct TQ as (Qlen & _ & Qlast & Qbytes).
    clear R2 R4 R5 R6 R7 R9 R10 R12 R16 R18 RH TPC OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, BATCHSZ, BATCHCAP, T_QC, SB, KSPACE, PTRLO in *.
    destruct (p16_facts (U p) Lp4 ltac:(lia)) as (_ & _ & _ & P8 & _ & _).
    destruct (sh_up8 (U p) m P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (shad_facts2 (U p) (up8 m) ltac:(clear -AB4 Hpr U8a; lia) ltac:(clear - Hpr; lia) ltac:(clear - AB2 CR; lia) U8b P8 U8d) as (D81 & D82 & D83 & D84 & D85 & D86).
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr; lia).
    assert (XdC2 : forall z, AIMGLO <= z < AIMGHI -> ~ X2 (U S) (U p) T m z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite <- SHhi, SHlo; rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr D84; lia).
    assert (XdT : forall z, T <= z < T + 2800 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b CP2 CPlo GTC; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b AB2 CP2 CPlo; lia).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ (PSIDE (U p) (up8 m) /\ U p + up8 m <= U S - 3584) /\ U p mod 16 = 0).
    { split; [clear - PIMG; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear -AB4 U8a; lia | clear - AB2 U8a CP2 CPlo; lia] | exact Lp4]. }
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    assert (Gn8m : 8 <= up8 m /\ up8 m mod 8 = 0 /\ up8 m <= 2 ^ 40) by (clear - U8a U8b U8c U8d M28 Lp3; lia).
    assert (GpTm : U p + up8 m <= T \/ T + 4096 <= U p - 16) by (clear - GpT; lia).
    (* [comment removed for export] *)
    assert (NST_stk : forall z, U S - 3584 <= z -> ~ (T + 2768 <= z < T + 3168)) by (intros z Hz; clear - Hz GTC CP2 CPlo; lia).
    assert (NST_p : forall z, U p - 16 <= z < U p + up8 m -> ~ (T + 2768 <= z < T + 3168)) by (intros z Hz; clear - Hz GpT; lia).
    assert (NST_sh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> ~ (T + 2768 <= z < T + 3168)).
    { intros z Hz. unfold sh_lo, sh_hi, SB in Hz. clear - Hz GTB Lp1 Lp2 Lp3 CR. Z.div_mod_to_equations. lia. }
    hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp GpTm.
    hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp D81. hidehyp GCI.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xd (U S) (U p) T (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    assert (NHsh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (B4 (U p) m HinP z Hz). }
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_mcsz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20)))) by konst EQ0 R1 NHs XdC CELL_mcsz.
    assert (K_msz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))) by konst EQ0 R1 NHs XdC CELL_msz.
    assert (K_gfl : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 FL))) by konst EQ0 R1 NHs XdC CELL_gfl.
    assert (K_mff : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (FL + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mff.
    assert (K_gsh : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konst EQ0 R1 NHs XdC CELL_gsh.
    assert (K_sh : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { cbn [ia_rtc_sb both_addrs] in Csb. cell0 EQ0 NHs XdC Csb. }
    assert (K_gmb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konst EQ0 R1 NHs XdC CELL_gmb.
    assert (K_mb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mb.
    assert (K_gme : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konst EQ0 R1 NHs XdC CELL_gme.
    assert (K_me : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konst EQ0 R1 NHs XdC CELL_me.
    assert (K_ghe : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konst EQ0 R1 NHs XdC CELL_ghe.
    assert (K_he : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konst EQ0 R1 NHs XdC CELL_he.
    assert (K_grm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konst EQ0 R1 NHs XdC CELL_grm.
    assert (K_rm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konst EQ0 R1 NHs XdC CELL_rm.
    assert (K_cpm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by lia. konst EQ0 R1 NHs XdC CELL_cpm. }
    (* [comment removed for export] *)
    assert (K_cnt0 : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (T + 2128) with (T + 208 + 80 * 24) by lia. cell0 EQ0 NHT XdT PCcnt. }
    assert (K_nhi : rdn BSEGS (mrestrict Hd M') (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnhi. }
    assert (K_nlo : rdn BSEGS (mrestrict Hd M') (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnlo. }
    (* [comment removed for export] *)
    assert (LCASE : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0))
                    \/ exists tq' b, a_tq st' = tq' ++ [b]
                        /\ rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b)))
                        /\ rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 1021))
                        /\ rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_tq st')))))
                        /\ (0x10007fff8000 <= ba_addr b /\ ba_addr b + 8192 <= U S - 3584)
                        /\ hide (ba_addr b + 8192 <= T \/ T + 4096 <= ba_addr b) /\ hide (ba_addr b + 8192 <= U p - 16 \/ U p + up8 m <= ba_addr b)
                        /\ 1 <= Z.of_nat (length (a_tq st')) < 2 ^ 40).
    { destruct TQC as [Etq | (tq' & b & Etq & FULL)].
      - left. rewrite Etq in Qlen. cbn [length Z.of_nat] in Qlen. cell0 EQ0 NHT XdT Qlen.
      - right. exists tq', b.
        assert (HinB : In b (a_tq st' ++ a_gq st')) by (apply in_app_iff; left; rewrite Etq; apply in_app_iff; right; left; reflexivity).
        destruct (OBL_batch_geom st' Lc FF b (U p) m W' HinB HinP) as (GBp & GBT & GBlo & GBhi).
        destruct (read_tq_last bt st' Lc FF M0 mdl' tq' b W' RP' Etq) as (Qlen' & Qlast' & _ & _ & _ & Bcnt & _ & _ & _ & Blen & Blob & Bhib).
        rewrite BT_segs in *. rewrite FULL in Bcnt. unfold BATCHCAP in Bcnt. unfold BATCHSZ in *.
        assert (NHbo : forall z, ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
        { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; right. exists b. split; [exact HinB | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
        assert (XdBo : forall z, ba_addr b <= z < ba_addr b + 8192 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GBp GBT GBhi U8b CP2 CPlo; lia).
        split; [exact Etq|]. split; [replace (T + 96) with (T + 80 + 16) by lia; cell0 EQ0 NHT XdT Qlast'|].
        split; [cell0 EQ0 NHbo XdBo Bcnt|]. split; [cell0 EQ0 NHT XdT Qlen'|].
        assert (LEN1 : 1 <= Z.of_nat (length (a_tq st'))) by (rewrite Etq, length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia).
        pose proof W' as (_ & _ & (QT & _ & QTB & _) & _). rewrite Forall_forall in QT.
        assert (IT : forall b0, In b0 (a_tq st') -> forall m0 n0, In (m0, n0) (ba_items b0) -> 1 <= n0).
        { intros b0 Hb0 m0 n0 Hin. destruct (QT b0 Hb0) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
        pose proof (q_bytes_ge (a_tq st') IT) as G1. unfold BATCHSZ in G1.
        split; [clear - GBlo GBhi CP2 CPlo; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hide in G in change_no_check G' end); clear - GBT; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hide in G in change_no_check G' end); clear - GBp; lia|].
        clear - LEN1 G1 QTB. lia. }
    clear Qlen Qlast Qbytes Hnhi Hnlo Csb R1 PCcnt OBL_batch_geom.
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))) by stk NHs Cq0.
    assert (S_q1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn BSEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn BSEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))) by stk NHs Cq3.
    assert (S_q4 : rdn BSEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn BSEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    assert (S_i0 : rdn BSEGS (mrestrict Hd M') (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))) by (rewrite <- CP1; stk NHs Ci0).
    assert (S_i1 : rdn BSEGS (mrestrict Hd M') (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn BSEGS (mrestrict Hd M') (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn BSEGS (mrestrict Hd M') (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn BSEGS (mrestrict Hd M') (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn BSEGS (mrestrict Hd M') (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn BSEGS (mrestrict Hd M') (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    clear Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS (mrestrict Hd M') (at_ S (-2304)) 2304 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      eapply store_ok_mono; [exact GRM|]. apply CPstk. cbn in Hx. rewrite <- CP2. lia. }
    assert (SOKp : store_ok BSEGS (mrestrict Hd M') p 8 = true).
    { rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHp].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKsh : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 (shad p)) (Z.to_nat (up8 m / 8)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by lia; lia | unorm; rewrite Z2Nat.id by lia; hoff NHsh].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WSH); unorm; rewrite ?Z2Nat.id by lia; lia. }
    assert (SOKT : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    clear WHDR WSH WBLK TW.
    (* [comment removed for export] *)
    assert (GS3 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gn3 : 1 <= m <= 2 ^ 28) by lia.
    assert (Gn83 : AsRtRegion.down8 (m + 7) = up8 m /\ m <= up8 m <= m + 7 /\ up8 m mod 8 = 0 /\ 8 <= up8 m) by (split; [apply down8_up8R1 | lia]).
    assert (Gfl3 : 0 <= FL /\ FL + 4096 <= AIMGHI) by lia.
    assert (Gmid3 : U (Z_to_bv 64 MIDEND) < 2 ^ 64) by (wd_ulia).
    assert (Ccpm1 : U (Z_to_bv 8 CPM) <> 0) by (rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (D20' : getr R' 20 = Z_to_bv 64 T) by exact Y20.
    (* [comment removed for export] *)
    assert (RUNX : exists rf, msteps BSEGS (mkst R' (0x50838%bv : word) (mrestrict Hd M') (seg_rom BSEGS))
                                           (mkst rf (0x5143c%bv : word) (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) (seg_rom BSEGS))
                              /\ refill_call_regs S p tp T m R' rf).
    { destruct LCASE as [C0 | (tq' & b & Etq & C1 & C2 & C3 & G1 & G2 & G3 & G4)].
      - destruct (run_p3r1e (mrestrict Hd M') (seg_rom BSEGS) R' S p tp (getr R 22)
                    T m (up8 m) id FL (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND))
          as (rf & RUN & REGS).
        all: try assumption.
        all: try reflexivity.
        all: try (unfold hide in *; assumption).
        all: let k := numgoals in guard k = 1.
        exists rf. exact (conj RUN REGS).
      - destruct (run_p3r1f (mrestrict Hd M') (seg_rom BSEGS) R' S p tp (getr R 22)
                    T m (up8 m) id FL (ba_addr b) (Z.of_nat (length (a_tq st'))) (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND))
          as (rf & RUN & REGS).
        all: try assumption.
        all: try reflexivity.
        all: try (unfold hide in *; assumption).
        all: let k := numgoals in guard k = 1.
        exists rf. exact (conj RUN REGS). }
    clear LCASE.
    destruct RUNX as (rf & RUN3 & Z1 & Z2 & Z10 & Z11 & Z12 & Z13 & Z8 & Z9 & Z18 & Z19 & Z21 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    (* [comment removed for export] *)
    replace (0x50838%bv : word) with (Z_to_bv 64 0x50838 : word) in RUN3 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS))
             (@mkst fx' rf (0x5143c%bv : word) (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) (seg_rom BSEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN3. }
    clear RUN3 K_mcsz K_msz K_gfl K_mff K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm K_cnt0 K_nhi K_nlo
          S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 SOKstk SOKp SOKsh SOKT.
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS))) with M' by reflexivity.
    replace (0x5143c%bv : word) with (Z_to_bv 64 0x5143c : word) by (apply bv_eq; reflexivity).
    pose proof (same_but_materialized_frame mdl' mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _ & _ & _ & Eeg1).
    remember (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as M13 eqn:EM13.
    set (M1 := munrestrict Hd M' M13).
    pose proof (Rep_sbm bt st' Lc FF M0 mdl' mdl1 RP' MI1 SBM1) as RP1.
    pose proof (fr_P3r1_grows (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as GR13. feed GR13. rewrite <- EM13 in GR13.
    assert (VIS : forall a : word, Hd a = false -> M1 a = M13 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M' M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRM1 : mem_grows M M1) by (eapply mem_grows_trans; [exact GRM | exact GR1]).
    pose proof (fr_P3r1_foot (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3F. feed P3F. rewrite <- EM13 in P3F.
    assert (FOOT1 : forall a : word, M1 a <> M' a ->
              (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (0x7fff8000 + U p / 8 <= U a < 0x7fff8000 + U p / 8 + up8 m / 8)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (P3F a NE). }
    assert (DIFF1 : forall a : word, M1 a <> M0 a -> X2 (U S) (U p) T m (U a) /\ M1 a <> None).
    { intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
      { destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0, GR1 in D. rewrite E1 in D. exact (D eq_refl). }
      (lazymatch goal with |- ?G => let G' := eval unfold X2 in G in change_no_check G' end). destruct (decide (M1 a = M' a)) as [E|N].
      - left. rewrite E in NE. exact (proj1 (DX a NE)).
      - destruct (FOOT1 a N) as [F|[F|F]]; [left; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2 in F; lia | left; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); lia | right; unfold sh_lo, sh_hi, SB in *; lia]. }
    (* [comment removed for export] *)
    apply (katD_bind BSEGS _ (refill24_post_k bt FXOK KR (X2 (U S) (U p) T m) st' Lc FF M1 mdl1 rf (at_ S (-2272)) (Z_to_bv 64 0x50c5c))).
    { apply (HYP_REFILL fx' (X2 (U S) (U p) T m) st' Lc FF M1 mdl1 rf (at_ S (-2272)) (Z_to_bv 64 0x50c5c) HFX').
      { rewrite Eh1. exact HH'. }
      { exact (model_ivs_wf_sbm mdl' mdl1 SBM1 MW'). }
      { exact W'. }
      { exists M0. split; [exact RP1 | exact DIFF1]. }
      { intros a Ha. unfold X2, Xd in Ha. rewrite CP2 in Ha.
        destruct Ha as [[Ha|[Ha|[Ha|Ha]]]|Ha]; [right; right; exists (U p), m; split; [exact HinP | lia] | right; right; exists (U p), m; split; [exact HinP | lia]
                                            | right; left; lia | left; lia | right; right; exists (U p), m; split; [exact HinP | right; right; exact Ha]]. }
      { exact ECA. }
      { destruct BD' as (_ & _ & BK). clear - BK KC1. lia. }                                (* [comment removed for export] *)
      { exact MUR1. }                                                                           (* [comment removed for export] *)
      { exact Z1. }
      { exact Z2. }
      { rewrite Z10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC in G in change_no_check G' end). unorm. reflexivity. }
      { rewrite Z11. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end). unorm. lia. }
      { rewrite Z12. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. reflexivity. }
      { rewrite Z13. reflexivity. }
      { rewrite Z4. rewrite ?BT_ia. exact CP4. }                                            (* [comment removed for export] *)
      { rewrite at_u by lia. rewrite CP2. apply sp_mod16_2272. exact CP16. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRM1. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
        - eapply store_ok_mono; [exact GRM1|]. apply CPstk. rewrite <- CP2. lia. }
      { (* [comment removed for export] *)
        intros c' FAIL.
        destruct FAIL as (fx2 & st2 & Mf & mdl2 & R2 & Ec' & HFX2 & HH2 & W2 & (M02 & RP2 & DX2) & A02).
        subst c'.
        pose proof RP2 as (R1f & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13f & R14f & _).
        rewrite BT_segs in R1f.
        destruct R14f as (B1f & B2f & _).
        destruct CELLSPIN as (CSP1 & CSP2 & CSP3).
        set (Hd2 := HID st2 mdl2).
        assert (NHs2 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd2 (Z_to_bv 64 z) = false).
        { intros z Hz Hr. apply (HID_off_zone bt st2 mdl2 z R13f Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
        assert (EQ2 : forall a : word, ~ X2 (U S) (U p) T m (U a) -> Mf a = M02 a).
        { intros a Ha. destruct (decide (Mf a = M02 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX2 a N))). }
        assert (KS1 : rdn BSEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1))) by konst EQ2 R1f NHs2 XdC2 CSP1.
        assert (KS2 : rdn BSEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0x105f60) 8 = Some (LE8 (Z_to_bv 64 0x19fcdc))) by konst EQ2 R1f NHs2 XdC2 CSP2.
        assert (KS3 : rdn BSEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ2 R1f NHs2 XdC2 CSP3.
        destruct (enq_spin_run (mrestrict Hd2 Mf) (seg_rom BSEGS) R2 A02 KS1 KS2 KS3) as (rs & RUNS).
        replace (0x50c5c%bv : word) with (Z_to_bv 64 0x50c5c : word) in RUNS by (apply bv_eq; reflexivity).
        apply (doomed_msteps_acct BSEGS Hd2 (HID_off_segments bt st2 Lc FF M02 mdl2 BT_ia RP2) asanF_segs_wx (a_aa st2)
                 (@mkst fx2 R2 (Z_to_bv 64 0x50c5c) Mf (seg_rom BSEGS)) (@mkst fx2 rs (0x50c98%bv : word) (mrestrict Hd2 Mf) (seg_rom BSEGS)) mdl2).
        { apply lazy_cover_HID. }
        { exact B1f. }
        { exact B2f. }
        { exact HH2. }
        { rewrite restrict_mkstF. exact RUNS. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
        pose proof (same_but_materialized_frame mdl2 mdl3 SBM3) as SF3.
        destruct SF3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        apply doomed_to_spin; [apply enq_spin_to_spin | rewrite Eh3; exact HH2]. } }
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx'' & st'' & M'' & mdl'' & R'' & ks & k & Ec' & HFX'' & HH'' & W'' & RX'' & ECA'' & Etq & Egq & Esec & Edep & Eia & Ekact & Eaa
                      & KEPT & CHG'' & LZ'' & RK & A0 & SEV'' & MW'' & HOLES).
    subst c'. apply katD_refl.
    destruct RX'' as (M0'' & RP'' & DX'').
    (* [comment removed for export] *)
    assert (STK : forall kk bs0, -2272 <= kk -> kk + 8 <= 0 -> rdn BSEGS M13 (at_ S kk) 8 = Some bs0 -> rdn BSEGS M'' (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS M'' M13); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite (KEPT x); [| (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); left; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | apply NST_stk; clear - Hx Hk1; lia].
      apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range | lia]. }
    pose proof (fr_P3r1_rdn_out (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3O. feed P3O. rewrite <- EM13 in P3O.
    assert (STKi : forall kk bs0, -56 <= kk -> kk + 8 <= 0 -> rdn BSEGS (mrestrict Hd M') (at_ S kk) 8 = Some bs0 -> rdn BSEGS M'' (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply STK; [lia | lia |].
      rewrite P3O; [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia]. }
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    pose proof (fr_P3r1_hdr16 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3H. feed P3H. rewrite <- EM13 in P3H.
    pose proof (fr_P3r1_shadow (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3S. feed P3S. rewrite <- EM13 in P3S.
    pose proof (fr_P3r1_e0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe0. feed Pe0. rewrite <- EM13 in Pe0.
    pose proof (fr_P3r1_e1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe1. feed Pe1. rewrite <- EM13 in Pe1.
    pose proof (fr_P3r1_e2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe2. feed Pe2. rewrite <- EM13 in Pe2.
    pose proof (fr_P3r1_e3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe3. feed Pe3. rewrite <- EM13 in Pe3.
    pose proof (fr_P3r1_e4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe4. feed Pe4. rewrite <- EM13 in Pe4.
    pose proof (fr_P3r1_e5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe5. feed Pe5. rewrite <- EM13 in Pe5.
    pose proof (fr_P3r1_e6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe6. feed Pe6. rewrite <- EM13 in Pe6.
    pose proof (fr_P3r1_cb0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pcb0. feed Pcb0. rewrite <- EM13 in Pcb0.
    pose proof (fr_P3r1_cb1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pcb1. feed Pcb1. rewrite <- EM13 in Pcb1.
    pose proof (fr_P3r1_q0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq0. feed Pq0. rewrite <- EM13 in Pq0.
    pose proof (fr_P3r1_q1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq1. feed Pq1. rewrite <- EM13 in Pq1.
    pose proof (fr_P3r1_q2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq2. feed Pq2. rewrite <- EM13 in Pq2.
    pose proof (fr_P3r1_q3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq3. feed Pq3. rewrite <- EM13 in Pq3.
    pose proof (fr_P3r1_q4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq4. feed Pq4. rewrite <- EM13 in Pq4.
    pose proof (fr_P3r1_q5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq5. feed Pq5. rewrite <- EM13 in Pq5.
    pose proof (fr_P3r1_q6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq6. feed Pq6. rewrite <- EM13 in Pq6.
    pose proof (fr_P3r1_q7 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq7. feed Pq7. rewrite <- EM13 in Pq7.
    (lazymatch goal with |- ?G => let G' := eval unfold putR1_post in G in change_no_check G' end). fold S. rewrite BT_ia.
    exists fx'', R'', M'', M0'', mdl'', st'', ks, k.
    split; [reflexivity|]. split; [exact HFX''|]. split; [exact HH''|]. split; [exact MW''|]. split; [exact W''|]. split; [exact RP''|].
    split. { unfold bounds in BD' |- *. rewrite Ekact. exact BD'. }
    split; [exact (hp_neut bt HP HPc FAM h st' st'' HLE (proj1 HOLES) (proj2 HOLES) Ekact)|]. split; [exact ECA''|]. split; [exact Etq|]. split; [exact Egq|]. split; [exact DX''|].
    split.
    { (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. destruct (decide (M'' a = M1 a)) as [E|N].
      + rewrite E in NE |- *. split; cycle 1.
        { destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:EMa; [|reflexivity]. exfalso.
          assert (X : M a <> None) by (rewrite EMa; discriminate). apply GRM1 in X. rewrite E1 in X. exact (X eq_refl). }
        destruct (decide (M1 a = M' a)) as [E2|N2].
        * rewrite E2 in NE. destruct (CHG a NE) as [Cg _]. rewrite CP2 in Cg |- *. (lazymatch goal with |- ?G => let G' := eval unfold X2 in G in change_no_check G' end).
          destruct Cg as [Cg|[Cg|[Cg|Cg]]]; [left; left; exact Cg | right; left; lia | right; right; left; exact Cg | right; right; right; exact Cg].
        * destruct (FOOT1 a N2) as [F|[F|F]]; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite CP2 in *.
          -- right; left. lia.
          -- left; left. lia.
          -- left; right. unfold sh_lo, sh_hi, SB in *. lia.
      + destruct (CHG'' a N) as [Cg D]. split; [| exact D]. rewrite BT_ia in Cg. rewrite at_u in Cg by lia. rewrite CP2 in Cg |- *.
        destruct Cg as [Cg|[Cg|Cg]]; [right; left; lia | right; right; left; exact Cg | right; right; right; exact Cg]. }
    split.
    { (* [comment removed for export] *) rewrite (KEPT (at_ p (-16))); [| (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | apply NST_p; rewrite at_u by lia; clear - U8a Lp3; lia].
      rewrite VIS by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply NHp; wd_ulia). rewrite P3H. rewrite MrM' by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply NHp; wd_ulia). exact Hb16. }
    split.
    { (* [comment removed for export] *) intros i Hi. rewrite KEPT; [| unfold X2, sh_lo, sh_hi, SB in *; right; wd_ulia | rewrite at_u by lia; unfold sh_lo, sh_hi, SB in *; wd_ulia | apply NST_sh; unfold sh_lo, sh_hi, SB in *; wd_ulia].
      rewrite VIS by (apply NHsh; unfold sh_lo, sh_hi, SB in *; lia). (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). apply P3S. exact Hi. }
    split. { repeat split; (apply STK; [lia | lia | assumption]). }
    split. { repeat split; (apply STK; [lia | lia | assumption]). }
    split. { split; [apply STKi; [lia | lia | fold ra0; rewrite CP1; exact S_i0] | repeat split; (apply STKi; [lia | lia | assumption])]. }
    split.
    { split; [exact A0|]. split; [viaRK RK 2 Z2|]. split; [viaRK RK 8 Z8|]. split; [viaRK RK 9 Z9|]. split; [viaRK RK 18 Z18|].
      split; [viaRK RK 19 Z19|]. split; [viaRK RK 21 Z21|]. split; [viaRK RK 22 Z22|]. split; [viaRK RK 3 (eq_trans Z3 Y3)|]. split; [viaRK RK 4 Z4|].
      split; [viaRK RK 23 (eq_trans Z23 Y23)|]. split; [viaRK RK 24 (eq_trans Z24 Y24)|]. split; [viaRK RK 25 (eq_trans Z25 Y25)|].
      split; [viaRK RK 26 (eq_trans Z26 Y26)|]. viaRK RK 27 (eq_trans Z27 Y27). }
    split.
    { eapply same_except_vm_trans; [exact SEV|]. eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV'']. }
    intros a Ha. rewrite <- BT_ia in Ha. rewrite (LZ'' a Ha). rewrite BT_ia in Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity | exact (LZ a Ha)].
  Qed.
End PUTR1.
End BoAllocFPutR1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR.BoAllocF5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB.BoAllocFTail OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR BoAllocFPutR1.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma nth_error_snocRe : forall {A} (l : list A) (x : A), nth_error (l ++ [x]) (length l) = Some x.
Proof. intros A l x. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Section PUTRE.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.            (* [comment removed for export] *)
  Hypothesis CELLSPIN : free_cells_spin bt.
  Variable KDR : Z.
  Hypothesis G_KDR : 0 <= KDR <= 1376.
  Hypothesis HYP_DRAIN : HYP_DRAIN_stmt bt FXOK KDR.
  (* [comment removed for export] *)
  Hypothesis OPS_WFX_newbatch : forall st Lc FF L1 L2 p n k ks,
    WF bt st Lc FF -> a_kact st <= KCAP -> Lc = L1 ++ (p, n) :: L2 -> a_cache st BATCHCLASS = ks ++ [k] ->
    WFX bt (op_quar_newbatch (op_cache_pop st BATCHCLASS) (chunk_of_compact (bt_spacebeg bt) BATCHCLASS k) (p - 16) n) (L1 ++ L2) FF.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition free_putRe_cont_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (ks : list Z) (k : Z),
      let S := getr R 2 in
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      a_tq st' = [] -> a_cache st' BATCHCLASS = ks ++ [k] -> m <= 2 ^ 28 ->
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> X2 (U S) (U p) T m (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (X2 (U S) (U p) T m (U a) \/ (U S - 3584 <= U a < U S)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      (forall i, 0 <= i < up8 m / 8 -> M' (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd)) ->
      rdn BSEGS M' (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)) -> rdn BSEGS M' (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728))) ->
      rdn BSEGS M' (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)) -> rdn BSEGS M' (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 m)) ->
      rdn BSEGS M' (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))) -> rdn BSEGS M' (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)) ->
      rdn BSEGS M' (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16))) ->
      rdn BSEGS M' (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)) -> rdn BSEGS M' (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) -> rdn BSEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn BSEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn BSEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)) ->
      rdn BSEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn BSEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS M' (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))) -> rdn BSEGS M' (at_ S (-2192)) 8 = Some (LE8 (getr R 22)) ->
      rdn BSEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn BSEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn BSEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn BSEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn BSEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn BSEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn BSEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 10 = Z_to_bv 64 1 -> getr R' 2 = at_ S (-2272) -> getr R' 8 = at_ (Z_to_bv 64 T) 2128 -> getr R' 9 = at_ (Z_to_bv 64 T) 208 ->
      getr R' 18 = at_ p (-16) -> getr R' 19 = at_ (Z_to_bv 64 T) 80 -> getr R' 21 = Z_to_bv 64 m -> getr R' 22 = Z_to_bv 64 (2 ^ 20) ->
      getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD BSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x50c5c) M' (seg_rom BSEGS)) mdl')
           (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl (L1 ++ L2) FF
                      (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp).

  Theorem free_putRe_cont : free_putRe_cont_stmt.
  Proof using FAM OPS_WFX_newbatch HYP_DRAIN G_KDR KDR GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putRe_cont_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' ks k CP HR10 ELc W' RP' BD' HLE ETQ ECA M28
           HFX' HH' MW' DX CHG Hb16 SHD Ce0 Ce1 Ce2 Ce3 Ce4 Ce5 Ce6 Ccb0 Ccb1 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Cq6 Cq7 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y10 Y2 Y8 Y9 Y18 Y19 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 SEV LZ.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & OBL_blk_geom & _ & OBL_hdr_writable & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    pose proof (OBL_cache_chunk_pf bt) as OBL_cache. unfold OBL_cache_chunk_stmt in OBL_cache.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    assert (HinK : In k (a_cache st' BATCHCLASS)) by (rewrite ECA; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    clear AB3 GCT' GCB.
    (* [comment removed for export] *)
    destruct (OBL_cache st' Lc FF M0 mdl' BATCHCLASS k W' RP' ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) HinK)
      as (Bcv & Blo & Bhi & B16 & Kr & BT & BC & BP & BB & Bnl & BW & Bpriv).
    set (ba := chunk_of_compact (bt_spacebeg bt) BATCHCLASS k) in *.
    change (csize BATCHCLASS) with 8192 in Bhi, BT, BC, BP, BB, Bnl, BW, Bpriv.
    assert (Eba : bt_spacebeg bt + 3 * 2 ^ 35 + 16 * k = ba) by ((lazymatch goal with |- ?G => let G' := eval unfold ba, chunk_of_compact, region_beg, KREGION, BATCHCLASS in G in change_no_check G' end); lia).
    specialize (BP (U p) m HinP).
    clear OBL_blk_geom OBL_cache.
    assert (T16 : T mod 16 = 0) by (clear -TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    pose proof W' as (_ & _ & (_ & _ & QTB & QGB & _) & _).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof R17 as Csb.
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    (* [comment removed for export] *)
    destruct TQ as (Qlen & _ & _ & Qbytes). rewrite ETQ in Qlen, Qbytes. cbn [length Z.of_nat q_bytes fold_right] in Qlen, Qbytes.
    destruct (TPC BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (PCcnt & _ & PCsz & PCk). rewrite ECA in PCcnt, PCk.
    rewrite length_app in PCcnt. cbn [length] in PCcnt. rewrite Nat2Z.inj_add in PCcnt. change (Z.of_nat 1) with 1 in PCcnt.
    specialize (PCk (length ks) k (nth_error_snocRe ks k)).
    unfold T_PC, PC_SZ, BATCHCLASS in PCcnt, PCsz, PCk.
    clear R2 R4 R5 R6 R7 R9 R10 R12 R16 R18 RH TPC OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, BATCHSZ, BATCHCAP, T_QC, SB, KSPACE, PTRLO in *.
    destruct (p16_facts (U p) Lp4 ltac:(lia)) as (_ & _ & _ & P8 & _ & _).
    destruct (sh_up8 (U p) m P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    pose proof (cache_len bt st' Lc FF W' BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as CL. rewrite ECA, length_app in CL. cbn [length] in CL.
    destruct (shad_facts2 (U p) (up8 m) ltac:(clear -AB4 Hpr U8a; lia) ltac:(clear - Hpr; lia) ltac:(clear - AB2 CR; lia) U8b P8 U8d) as (D81 & D82 & D83 & D84 & D85 & D86).
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ X2 (U S) (U p) T m z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite <- SHhi, SHlo; rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr D84; lia).
    assert (XdT : forall z, T <= z < T + 2800 -> ~ X2 (U S) (U p) T m z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite <- SHhi, SHlo; clear - Hz GpT U8b CP2 CPlo GTC GTB D82 D84 PIMG; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ X2 (U S) (U p) T m z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite <- SHhi, SHlo; clear - Hz GpT U8b AB2 AB4 CP2 CPlo D82 D84 PIMG; lia).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ (PSIDE (U p) (up8 m) /\ U p + up8 m <= U S - 3584) /\ U p mod 16 = 0).
    { split; [clear - PIMG; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear -AB4 U8a; lia | clear - AB2 U8a CP2 CPlo; lia] | exact Lp4]. }
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    assert (Gn8m : 8 <= up8 m /\ up8 m mod 8 = 0 /\ up8 m <= 2 ^ 40) by (clear - U8a U8b U8c U8d M28 Lp3; lia).
    assert (Gbam : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584) by (clear - Blo Bhi CP2 CPlo; lia).
    assert (GbaTm : ba + 8192 <= T \/ T + 4096 <= ba) by (clear - BT; lia).
    assert (Gbapm : ba + 8192 <= U p - 16 \/ U p + up8 m <= ba) by (clear - BP; lia).
    assert (GpTm : U p + up8 m <= T \/ T + 4096 <= U p - 16) by (clear - GpT; lia).
    assert (GbapM : hideM (ba + 8192 <= U p - 16 \/ U p + 8 <= ba)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideM in G in change_no_check G' end); clear - Gbapm U8b; lia).
    assert (GpTM : hideM (U p + 8 <= T \/ T + 4096 <= U p - 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideM in G in change_no_check G' end); clear - GpTm U8b; lia).
    assert (GbaTM : hideM (ba + 8192 <= T \/ T + 4096 <= ba)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideM in G in change_no_check G' end); exact GbaTm).
    assert (Gp2 : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584) by (destruct Gpm as (X1 & (_ & X2') & _); clear - X1 X2' U8b; lia).
    hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp BT. hidehyp BC. hidehyp BP. hidehyp GbaTm. hidehyp Gbapm. hidehyp GpTm.
    hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp D81. hidehyp GCI.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ X2 (U S) (U p) T m (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    assert (NHb : forall z, ba <= z < ba + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply Bnl. exact Hz. }
    assert (NHsh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (B4 (U p) m HinP z Hz). }
    assert (LZT : forall z, T <= z < T + 4096 -> lzb mdl' z = false).
    { intros z Hz. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    clear OBL_nolazy_rt Bnl.
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_spb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 (bt_spacebeg bt)))).
    { unfold free_cells_nb, IB in CELLNB. rewrite BT_ia in CELLNB. cbn [ia_instance both_addrs Z.add] in CELLNB. konst EQ0 R1 NHs XdC CELLNB. }
    (* [comment removed for export] *)
    assert (K_len : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0))) by cell0 EQ0 NHT XdT Qlen.
    assert (K_qb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st'))))).
    { rewrite ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). replace (T + 104) with (T + 80 + 24) by lia. cell0 EQ0 NHT XdT Qbytes. }
    assert (K_cnt24 : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat (length ks) + 1)))).
    { replace (T + 2128) with (T + 208 + 80 * 24) by lia. cell0 EQ0 NHT XdT PCcnt. }
    assert (K_cs : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2136)) 8 = Some (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))).
    { replace (T + 2136) with (T + 208 + 80 * 24 + 8) by lia. cell0 EQ0 NHT XdT PCsz. }
    assert (K_k : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2144 + 4 * (Z.of_nat (length ks) + 1 - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k))).
    { replace (T + 2144 + 4 * (Z.of_nat (length ks) + 1 - 1)) with (T + 208 + 80 * 24 + 16 + 4 * Z.of_nat (length ks)) by lia. cell0 EQ0 NHT XdT PCk. }
    destruct (rdn_defined_ex BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2784)) 8) as (bst & K_st & Lst).
    { intros i Hi. rewrite mrestrict_off; [| apply NHT; revert Hi; unorm; intros Hi; lia]. apply GR0.
      apply (writableZ_def M0 _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    clear Qlen Qbytes PCcnt PCsz PCk Hnhi Hnlo Csb R1.
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))) by stk NHs Cq0.
    assert (S_q1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn BSEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn BSEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))) by stk NHs Cq3.
    assert (S_q4 : rdn BSEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn BSEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    assert (S_q6 : rdn BSEGS (mrestrict Hd M') (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81)))) by stk NHs Cq6.
    assert (S_q7 : rdn BSEGS (mrestrict Hd M') (at_ S (-2192)) 8 = Some (LE8 (getr R 22))) by stk NHs Cq7.
    assert (S_e0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc))) by stk NHs Ce0.
    assert (S_e1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728)))) by stk NHs Ce1.
    assert (S_e2 : rdn BSEGS (mrestrict Hd M') (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80))) by stk NHs Ce2.
    assert (S_e3 : rdn BSEGS (mrestrict Hd M') (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 m))) by stk NHs Ce3.
    assert (S_e4 : rdn BSEGS (mrestrict Hd M') (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Ce4.
    assert (S_e5 : rdn BSEGS (mrestrict Hd M') (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208))) by stk NHs Ce5.
    assert (S_e6 : rdn BSEGS (mrestrict Hd M') (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16)))) by stk NHs Ce6.
    assert (S_cb0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208))) by stk NHs Ccb0.
    assert (S_cb1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Ccb1.
    assert (S_i0 : rdn BSEGS (mrestrict Hd M') (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))) by (rewrite <- CP1; stk NHs Ci0).
    assert (S_i1 : rdn BSEGS (mrestrict Hd M') (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn BSEGS (mrestrict Hd M') (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn BSEGS (mrestrict Hd M') (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn BSEGS (mrestrict Hd M') (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn BSEGS (mrestrict Hd M') (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn BSEGS (mrestrict Hd M') (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    clear Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Cq6 Cq7 Ce0 Ce1 Ce2 Ce3 Ce4 Ce5 Ce6 Ccb0 Ccb1 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6.
    (* [comment removed for export] *)
    assert (SOKT : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    assert (SOKba : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 ba) 32 = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHb].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ BW); wd_ulia_c. }
    clear WHDR WSH WBLK TW BW.
    (* [comment removed for export] *)
    assert (GS3 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; clear - CPlo CPhi CR; lia).
    assert (GT3 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0) by (destruct GTm as (X1 & X2' & X3); repeat split; assumption).
    assert (Gn3 : 1 <= m <= 2 ^ 28) by lia.
    assert (Gqb3 : 0 <= q_bytes (a_tq st') <= 2 ^ 20) by (rewrite ETQ; (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end); lia).
    assert (Gcnt24 : 1 <= Z.of_nat (length ks) + 1 <= 16) by (clear - CL; lia).
    assert (Gk3 : 0 <= k < 2 ^ 32) by exact Kr.
    assert (Gspb : 0 <= bt_spacebeg bt) by (clear - SB0; lia).
    assert (Gba3 : AIMGHI <= ba /\ ba + 8192 <= U S - 3584) by (clear - Gbam; lia).
    assert (Lbcs : length (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0))) = 8%nat) by apply length_N_to_le_bytes.
    assert (Glen0 : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0))) by exact K_len.
    (* [comment removed for export] *)
    destruct (er2e_run (mrestrict Hd M') (seg_rom BSEGS) S p T m (Z.of_nat (length ks) + 1) k (bt_spacebeg bt) ba (q_bytes (a_tq st'))
                bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0))) R')
      as (rf & RUN3 & Z2 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    all: try assumption.
    all: try reflexivity.
    all: try (unfold hide in *; assumption).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    replace (0x50c5c%bv : word) with (Z_to_bv 64 0x50c5c : word) in RUN3 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x50c5c) M' (seg_rom BSEGS))
             (@mkst fx' rf (0x50c04%bv : word) (fr_e2e (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) (seg_rom BSEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN3. }
    clear RUN3 K_spb K_len K_qb K_cnt24 K_cs K_k K_st Glen0 SOKT SOKba.
    intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x50c5c) M' (seg_rom BSEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl3 SBM3) as SF3.
    destruct SF3 as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _ & _ & _ & Eeg3).
    remember (fr_e2e (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as M13 eqn:EM13.
    set (Mfin := munrestrict Hd M' M13).
    pose proof (fr_e2e_grows (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as GR13.
    rewrite <- EM13 in GR13.
    assert (VIS : forall a : word, Hd a = false -> Mfin a = M13 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    (* [comment removed for export] *)
    pose proof (fr_e2e_foot (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) ba bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3F.
    feed P3F. rewrite <- EM13 in P3F.
    assert (DIFF3 : forall a : word, Mfin a <> M' a ->
              (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (P3F a NE). }
    (* [comment removed for export] *)
    assert (PRIVp : forall z, (U p - 16 <= z < U p + up8 m \/ sh_lo (U p) <= z < sh_hi (U p) m) -> rt_priv both_addrs (L1 ++ L2) FF z).
    { intros z Hz. exact (OBL_freed_private st' Lc FF L1 L2 (U p) m z W' ELc Hz). }
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv both_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (OBL_rt_private st' Lc FF z W' ltac:(left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact Hz)) as (Z1' & Z2' & Z3').
      split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    assert (PRIVB : forall z, ba <= z < ba + 8192 -> rt_priv both_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (Bpriv z Hz) as (Z1' & Z2' & Z3'). split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    clear OBL_freed_private OBL_rt_private Bpriv.
    (* [comment removed for export] *)
    assert (XS : forall kk bs0, -2304 <= kk -> kk + 8 <= 0 -> rdn BSEGS M13 (at_ S kk) 8 = Some bs0 -> rdn BSEGS Mfin (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS Mfin M13); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range|]. rewrite at_u in Hx by lia. cbn in Hx. lia. }
    pose proof (fr_e2e_stack (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3K.
    feed P3K. rewrite <- EM13 in P3K.
    assert (XH : forall kk bs0, -2304 <= kk -> kk + 8 <= 0 -> rdn BSEGS (mrestrict Hd M') (at_ S kk) 8 = Some bs0 -> rdn BSEGS M13 (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply P3K; [lia | lia | exact Hr]. }
    replace (0x50c04%bv : word) with (Z_to_bv 64 0x50c04 : word) by (apply bv_eq; reflexivity).
    apply (free_put_tail bt FXOK KDR BT_segs BT_ia GEOM G_KDR HYP_DRAIN HP HPc FAM
             h fx' R rf M Mfin mdl mdl3 (L1 ++ L2) FF (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp
             (op_quar_newbatch (op_cache_pop st' BATCHCLASS) ba (U p - 16) m) p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81))
             (Z_to_bv 64 m) (at_ S (-2128)) (at_ (Z_to_bv 64 T) 208) (at_ p (-16))).
    all: rewrite ?BT_ia.
    - exact CP1.
    - exact CPr.
    - exact CPe.
    - exact CP2.
    - exact CP16.
    - exact CPlo.
    - exact CPhi.
    - exact CP4.
    - exact HFX'.
    - rewrite Eh3. exact HH'.
    - exact (model_ivs_wf_sbm mdl' mdl3 SBM3 MW').
    - (lazymatch goal with |- ?G => let G' := eval unfold ba in G in change_no_check G' end). exact (OPS_WFX_newbatch st' Lc FF L1 L2 (U p) m k ks W' (hp_kcap bt HP HPc FAM h st' HLE) ELc ECA).
    - (* [comment removed for export] *)
      assert (XF : forall c bs0, 0 <= c -> c + 8 <= 2 ^ 64 -> (forall z, c <= z < c + 8 -> Hd (Z_to_bv 64 z) = false) ->
                rdn BSEGS M13 (Z_to_bv 64 c) 8 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 c) 8 = Some bs0).
      { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same BSEGS Mfin M13); [| wd_ulia_c | exact Hr].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      pose proof (fr_e2e_hdr16 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3H. feed P3H.
      pose proof (fr_e2e_shad (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3S. feed P3S.
      pose proof (fr_e2e_b0 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb0. feed Pb0.
      pose proof (fr_e2e_b8 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb8. feed Pb8.
      pose proof (fr_e2e_b16 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb16. feed Pb16.
      pose proof (fr_e2e_b24 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb24. feed Pb24.
      pose proof (fr_e2e_q80 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq80. feed Pq80.
      pose proof (fr_e2e_q88 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq88. feed Pq88.
      pose proof (fr_e2e_q96 (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq96. feed Pq96.
      pose proof (fr_e2e_qb (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq104. feed Pq104.
      pose proof (fr_e2e_cnt (mrestrict Hd M') S p T m (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pcnt. feed Pcnt.
      rewrite <- EM13 in P3H, P3S, Pb0, Pb8, Pb16, Pb24, Pq80, Pq88, Pq96, Pq104, Pcnt.
      assert (XF4 : forall c bs0, 0 <= c -> c + 4 <= 2 ^ 64 -> (forall z, c <= z < c + 4 -> Hd (Z_to_bv 64 z) = false) ->
                rdn BSEGS M13 (Z_to_bv 64 c) 4 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 c) 4 = Some bs0).
      { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same BSEGS Mfin M13); [| wd_ulia_c | exact Hr].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      apply (OPS_REP_quar_newbatch2x_pf bt st' Lc FF L1 L2 M0 Mfin mdl' mdl3 (U p) m k ks W' RP' ELc ECA).
      * (* [comment removed for export] *)
        intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
        { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
          assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0, GRfin' in D. rewrite EF in D. exact (D eq_refl). }
        (lazymatch goal with |- ?G => let G' := eval unfold foot_quar_newbatch in G in change_no_check G' end). rewrite ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC, T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end).
        destruct (decide (Mfin a = M' a)) as [E|N].
        { rewrite E in NE. destruct (DX a NE) as [X _]. unfold X2, Xd in X. rewrite CP2 in X.
          destruct X as [[X|[X|[X|X]]]|X]; [left; exact X | right; left; exact X | do 7 right; left; lia | do 8 right; lia | right; right; left; exact X]. }
        destruct (DIFF3 a N) as [X|[X|[X|X]]].
        { do 3 right; left. exact X. }
        { do 4 right; left. lia. }
        { do 6 right; left. lia. }
        { do 7 right; left. lia. }
      * (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. apply heap_rdn1; [wd_ulia|].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
        assert (Eh : Hd (at_ p (-16)) = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ p (-16))); rewrite at_u by lia; apply NHp; lia).
        rewrite (VIS _ Eh). rewrite P3H. rewrite (MrM' _ Eh). exact Hb16.
      * (* [comment removed for export] *)
        intros g Hg. pose proof (granule_idx (U p) m g P8 Hg) as GI.
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. unfold user_granule in Hg. apply heap_rdn1; [(lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); wd_ulia|].
        assert (Eh : Hd (Z_to_bv 64 (SB + g)) = false) by (apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); lia).
        rewrite (VIS _ Eh).
        assert (E2 : M13 (Z_to_bv 64 (SB + g)) = mrestrict Hd M' (Z_to_bv 64 (SB + g))).
        { replace (SB + g) with (SB + U p / 8 + (g - U p / 8)) by lia. apply P3S; clear - GI D82; lia. }
        rewrite E2, (MrM' _ Eh). replace (SB + g) with (SB + U p / 8 + (g - U p / 8)) by lia. apply SHD. exact GI.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb0.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). replace (8192 + m) with (m + 8192) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb8.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb16.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). exact Pb24.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Z.add] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end).
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq80.
      * intros _. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 8) with (T + 88) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq88.
      * intros b0 q0 Eb. exfalso. rewrite ETQ in Eb. discriminate.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 16) with (T + 96) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq96.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC, BATCHSZ in G in change_no_check G' end). replace (T + 80 + 24) with (T + 104) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq104.
      * intros tq' b Etq. exfalso. rewrite ETQ in Etq. destruct tq'; discriminate.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end). replace (T + 208 + 80 * 24) with (T + 2128) by lia.
        replace (Z.of_nat (length ks)) with (Z.of_nat (length ks) + 1 - 1) by lia.
        apply XF4; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pcnt.
      * exact SBM3.
      * exact MI3.
    - (* [comment removed for export] *)
      assert (PH0 : 0 <= PHI (L1 ++ L2)).
      { apply PHI_nonneg. intros q n0 Hin.
        assert (Hin' : In (q, n0) Lc).
        { rewrite ELc. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
        destruct (live_range bt _ _ _ W' q n0 Hin') as (_ & _ & X & _). lia. }
      unfold bounds in BD' |- *. (lazymatch goal with |- ?G => let G' := eval cbn [a_kact op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end).
      rewrite ELc in BD'. rewrite PHI_app in BD' |- *. cbn [PHI snd fst] in BD'. rewrite length_app in BD' |- *. cbn [length] in BD'.
      rewrite PHI_app in PH0. unfold kcost_free, MBLK in *.
      destruct BD' as (BDa & BDb & BDc). split; [lia|]. split; [lia|]. lia.
    - (* [comment removed for export] *)
      apply (hp_neut bt HP HPc FAM h st' _ HLE); [| exact (fk_trans _ _ _ (fk_cache_pop bt st' BATCHCLASS (or_introl eq_refl)) (fk_quar_newbatch _ _ _ _)) | reflexivity].
      intros h' H'. unfold holes_le in H' |- *. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). exact H'.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_gq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). exact QGB.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_tq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate E.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_tq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). rewrite q_bytes_app, ETQ.
      replace (q_bytes [BATCH ba [(U p - 16, m)]]) with (BATCHSZ + (m + 0) + 0) by reflexivity.
      replace (q_bytes []) with 0 by reflexivity. clear - M28 Lp3. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia.
    - (* [comment removed for export] *)
      intros z Hz. transitivity (lzb mdl' z); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZT. exact Hz.
    - exact Z2. - exact Z22. - rewrite Z3; exact Y3. - rewrite Z4; exact Y4. - rewrite Z23; exact Y23. - rewrite Z24; exact Y24.
    - rewrite Z25; exact Y25. - rewrite Z26; exact Y26. - rewrite Z27; exact Y27.
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e0]].
    - (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). apply XS; [lia | lia | apply XH; [lia | lia | exact S_e1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e2]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e3]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e4]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e5]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_e6]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_cb0]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_cb1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q0]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q2]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q3]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q4]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q5]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q6]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_q7]].
    - apply XS; [lia | lia | apply XH; [lia | lia | fold ra0; rewrite CP1; exact S_i0]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i2]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i3]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i4]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i5]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i6]].
    - (* [comment removed for export] *)
      intros a Ha. rewrite <- CP2 in Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [clear - Ha CPlo CP2 CR; lia|]. apply CPstk. rewrite <- CP2. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. lia.
    - (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite <- CP2. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end).
      destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|[X|X]]] _].
        - unfold X2, Xd in X. destruct X as [[X|[X|[X|X]]]|X].
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVT. lia.
          + left. lia.
          + right; left. apply PRIVp. right. exact X.
        - left. lia.
        - right; left. destruct X as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. intros V. apply X3. rewrite ELc. apply app_visible_mono. exact V.
        - right; right; left. exact X. }
      destruct (DIFF3 a N) as [X|[X|[X|X]]].
      + right; left. apply PRIVB. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVT. lia.
    - exact GRfin.
    - eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM3].
    - (* [comment removed for export] *) intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZ.
      destruct Ha as [V|[V|V]]; [left; rewrite ELc; apply app_visible_mono; exact V | right; left; exact V | right; right; exact V].
  Qed.

  (* [comment removed for export] *)
  Definition free_putRe_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z),
      let S := getr R 2 in
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      a_tq st' = [] -> a_cache st' BATCHCLASS = [] -> m <= 2 ^ 28 -> K1 <= KCAP -> mu_room st' ->
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      rdn BSEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) -> rdn BSEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn BSEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn BSEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)) ->
      rdn BSEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn BSEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn BSEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn BSEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn BSEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn BSEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn BSEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn BSEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 2 = at_ S (-2176) -> getr R' 8 = at_ p (-16) -> getr R' 9 = at_ S (-2128) -> getr R' 10 = Z_to_bv 64 id ->
      getr R' 18 = Z_to_bv 64 (IB bt) -> getr R' 19 = Z_to_bv 64 0 -> getr R' 20 = Z_to_bv 64 T -> getr R' 21 = at_ S (-81) ->
      getr R' 22 = getr R 22 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      0 <= id < 2 ^ 32 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD BSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS)) mdl')
           (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl (L1 ++ L2) FF
                      (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp).

  Theorem free_putRe : free_putRe_stmt.
  Proof using FAM OPS_WFX_newbatch HYP_DRAIN G_KDR KDR CELLSPIN HYP_REFILL G_KR KR G_KD GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putRe_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id CP HR10 ELc W' RP' BD' HLE ETQ ECA M28 KC1 MUR1
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    apply (katD_bind BSEGS _ (putR1_post bt FXOK HPc h R M mdl Lc FF B C K1 m p st')).
    { pose proof (free_putR1 bt FXOK TP TSDP PGP FL MIDEND CPM KD BT_segs BT_ia CELLS GEOM G_KD KR G_KR HYP_REFILL CELLSPIN HP HPc FAM) as PR1.
      unfold free_putR1_stmt in PR1.
      apply (PR1 h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id); try assumption.
      left. exact ETQ. }
    intros c' POST. unfold putR1_post in POST.
    destruct POST as (fx'' & R'' & M'' & M0'' & mdl'' & st'' & ks & k & Ec' & HFX'' & HH'' & MW'' & W'' & RP'' & BD'' & HLE'' & ECA'' & Etq'' & Egq''
                      & DX'' & CHG'' & Hb16'' & SHD'' & (Ce0 & Ce1 & Ce2 & Ce3 & Ce4 & Ce5 & Ce6 & Ccb0 & Ccb1)
                      & (Dq0 & Dq1 & Dq2 & Dq3 & Dq4 & Dq5 & Dq6 & Dq7) & (Di0 & Di1 & Di2 & Di3 & Di4 & Di5 & Di6)
                      & (V10 & V2 & V8 & V9 & V18 & V19 & V21 & V22 & V3 & V4 & V23 & V24 & V25 & V26 & V27) & SEV'' & LZ'').
    subst c'.
    apply (free_putRe_cont h fx'' R R'' M M'' M0'' mdl mdl'' Lc FF L1 L2 B C K1 ret sp m p st'' ks k); try assumption.
    rewrite Etq''. exact ETQ.
  Qed.
End PUTRE.

