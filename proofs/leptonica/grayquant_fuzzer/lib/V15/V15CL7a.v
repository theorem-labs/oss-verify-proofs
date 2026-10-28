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
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
Module V15LeptDestroyNull.
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
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
(* [comment removed for export] *)









Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].

Lemma pixDestroy_null_W : forall (fx : FPState) C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> (forall x : word, ~ (s - 32 <= u x < s)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 94372) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pp ret S CK HW0 H2 Hlo Hpp Hhi0 ALpp H1 Hret H10 Cpp HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 32)%Z) by lia.
  assert (GLO2 : (s - 32 + Z.of_nat (Z.to_nat 32) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (32 <= s)%Z) by lia.
  assert (RRpp : (0 <= pp < 2 ^ 64)%Z) by lia.
  pose proof Cpp as Cpp0. rewrite <- (Z.add_0_r pp) in Cpp0.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 32) (Z.to_nat 32) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 415784 m0]) (EVar 35) (EVar 32) (exW_canary SEGS 415784 m0) s 32 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 63); KAlign (EVar 34) 8; KDisj (SA (EVar 32) (-32)) 32 (SA (EVar 34) 0) 8; KWord (SA (EVar 34) 0) 8 (ELit 0)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 32 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 32 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  apply (HC M0 RcF HWs0).
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - exact PMs0.
  - exact FRs0.
Qed.
End Chain.
End V15LeptDestroyNull.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15_code_15000_16000.
Module V15LeptErr.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15_code_15000_16000.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Err.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.

#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section RetErr.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rep_A : forall regs m (s msg proc : Z) (ret val : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 msg ->
    getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
    exists regs',
      msteps SEGS (mkst regs (0x155bc : word) m rom)
                  (mkst regs' (0x15520 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x155dc
      /\ getr regs' 10 = Z_to_bv 64 0x11483 /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_154b8 D_154b8 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_154bc D_154bc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_154c0 D_154c0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_154c4 D_154c4.                                                     (* [comment removed for export] *)
      sn F_154c8 D_154c8.                                                     (* [comment removed for export] *)
      sn F_154cc D_154cc.                                                     (* [comment removed for export] *)
      sn F_154d0 D_154d0.                                                     (* [comment removed for export] *)
      sn F_154d4 D_154d4.                                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_B : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) ->
    exists regs',
      msteps SEGS (mkst regs (0x155dc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_154d8 D_154d8.                                                     (* [comment removed for export] *)
      stepLD8 F_154dc D_154dc ret.                                            (* [comment removed for export] *)
      stepLD8 F_154e0 D_154e0 s0v.                                            (* [comment removed for export] *)
      zv F_154e4 D_154e4 (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_154e8 D_154e8 ret ltac:(bveq).                                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End RetErr.

(* [comment removed for export] *)
Lemma rdn_after : forall (m m' : word -> option byte) (lo hi a : Z) (n : nat) bs,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> (hi <= a \/ a + Z.of_nat n <= lo)%Z ->
  rdn SEGS m (Z_to_bv 64 a) n = Some bs -> rdn SEGS m' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros m m' lo hi a n bs OUT Ha Hn Hd R. rewrite <- R. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma returnErrorPtr_W : forall C A m md regs (s msg proc : Z) kmsg kproc (ret val : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
  str16 msg kmsg -> str16 proc kproc ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - (16 + LSF) <= u a < s)%Z -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' -> getr regs' 10 = val ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x155bc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rep_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x155dc) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rep_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x155dc) with (0x155dc : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply HK.
  - exact HW2.
  - intros a Ha. rewrite OUT2 by lia. subst M1. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
  - eapply mem_grows_trans; [|exact GR2]. subst M1. eapply mem_grows_trans; apply wbytes_grows.
  - apply cs_kept_intro; csr; try reflexivity.
  - csr. reflexivity.
Qed.

Section RetErrI.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rei_A : forall regs m (s msg proc : Z) (ret val : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 msg ->
    getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
    exists regs',
      msteps SEGS (mkst regs (0x154ec : word) m rom)
                  (mkst regs' (0x15520 : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x1550c
      /\ getr regs' 10 = Z_to_bv 64 0x11483 /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_153e8 D_153e8 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_153ec D_153ec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_153f0 D_153f0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_153f4 D_153f4.                                                     (* [comment removed for export] *)
      sn F_153f8 D_153f8.                                                     (* [comment removed for export] *)
      sn F_153fc D_153fc.                                                     (* [comment removed for export] *)
      sn F_15400 D_15400.                                                     (* [comment removed for export] *)
      sn F_15404 D_15404.                                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rei_B : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) ->
    exists regs',
      msteps SEGS (mkst regs (0x1550c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_15408 D_15408.                                                     (* [comment removed for export] *)
      stepLD8 F_1540c D_1540c ret.                                            (* [comment removed for export] *)
      stepLD8 F_15410 D_15410 s0v.                                            (* [comment removed for export] *)
      zv F_15414 D_15414 (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_15418 D_15418 ret ltac:(bveq).                                (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End RetErrI.

(* [comment removed for export] *)
Lemma returnErrorInt_W : forall C A m md regs (s msg proc : Z) kmsg kproc (ret val : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 proc -> getr regs 12 = val ->
  str16 msg kmsg -> str16 proc kproc ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - (16 + LSF) <= u a < s)%Z -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' -> getr regs' 10 = val ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x154ec : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hu16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rei_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x1550c) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rei_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x1550c) with (0x1550c : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply HK.
  - exact HW2.
  - intros a Ha. rewrite OUT2 by lia. subst M1. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
  - eapply mem_grows_trans; [|exact GR2]. subst M1. eapply mem_grows_trans; apply wbytes_grows.
  - apply cs_kept_intro; csr; try reflexivity.
  - csr. reflexivity.
Qed.

End Err.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V15LeptErr.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
Module V15LeptG.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import V15Kit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
(* [comment removed for export] *)








Import V15Kit.V15Reloc. Import V15Kit.V15RelocVL.


Lemma v15_LL : LLU16 = @LeptBase.LLG v15_reloc v15_lept.
Proof. reflexivity. Qed.

Definition v15_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @V15Pins AL CL) : @LeptBase.PinsG v15_reloc AL CL :=
  @LeptBase.Build_PinsG v15_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
End V15LeptG.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecT.
Module V15LeptPixClone.
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
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
(* [comment removed for export] *)










Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_pixClone : Z := 96700.

Lemma pixClone_W : forall (fx : FPState) C A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  PIXat m pix v -> p_rc v = 1%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall (m' : word -> option byte) regs', m' = wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2) -> W C A m' md -> cs_kept regs regs' ->
     getr regs' 10 = Z_to_bv 64 pix ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixClone) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pix v ret S CK HW0 H2 Hlo Hhi H1 Hret H10 PX Hrc Lpix_a0 F0pix HC.
  unfold PC_pixClone.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 16)%Z) by lia.
  assert (GLO2 : (s - 16 + Z.of_nat (Z.to_nat 16) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (16 <= s)%Z) by lia.
  clear PM0 SUB0. pose proof (POSTM_refl C (c_A0 C) s m0) as PM0. pose proof (w_keep _ _ _ _ HW0) as SUB0.
  pose proof PX as (Hp0 & Hp64 & _). assert (RRpix : (0 <= pix < 2 ^ 64)%Z) by lia.
  pose proof F0pix as Fpix.
  pose proof (PIX_rd_rc SEGS m0 pix v PX) as Crc. rewrite Hrc in Crc.
  pose proof (exW_kwr_blk2 SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 415784 m0]) (EVar 34) pix 64 p16_segs CK HW0 Lpix_a0 RRpix eq_refl eq_refl) as HKw.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pix 64 CK HW0 Lpix_a0 eq_refl RRpix GLO1) as WAPpix.
  destruct (exW_blk_rng C A0 m0 _ pix 64 CK HW0 Lpix_a0 RRpix eq_refl) as (Gp1 & Gp2 & Gp3).
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpix_a0) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 16) (Z.to_nat 16) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 415784 m0]) (EVar 35) (EVar 32) (exW_canary SEGS 415784 m0) s 16 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-16)) 16 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 20) 4 (ELit 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKw HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKw HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C (c_A0 C) s m0 M0).
  { subst M0. apply (exW_win_blks C A0 (c_A0 C) m0 _ E0 log0 (EVar 32) s 16 [(EVar 34, pix, 64%Z)] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRpix (conj Lpix_a0 (conj Fpix F0pix))))|]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pix)]).
  exW_regfactB BSF HR ex_r10 G10.
  assert (EM : M0 = wbytes m0 (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 2)).
  { subst M0 log0. cbn [mem_denot]. unfold adenot. cbn [a_base a_off]. change (edenot E0 (EVar 34)) with (Z_to_bv 64 pix). rewrite zbv_addi.
    change (edenot E0 (ELit 2)) with (Z_to_bv 64 2). rewrite (w2b_Z 4 2) by lia. reflexivity. }
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  apply (HC M0 RcF EM HWs0).
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - exact G10.
Qed.
End Chain.
End V15LeptPixClone.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL1a.
Module V15LeptQFill.
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
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL1a.
(* [comment removed for export] *)










Import V15CL1a.V15QFillBlk.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition QFA_HEAD : Z := 0x1dfc8.
Definition QFA_EXIT : Z := 0x1dffc.
Definition QFB_HEAD : Z := 0x1e0dc.
Definition QFB_EXIT : Z := 0x1e110.
Definition ex_r21 : reg := 21%bv. Definition ex_r23 : reg := 23%bv. Definition ex_r24 : reg := 24%bv. Definition ex_r25 : reg := 25%bv.

Ltac qf_get :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; lia end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; qf_get end ].

Section QFill.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Variables (p j0 v : Z).
Variable M0 : word -> option byte.
Hypothesis Rp : (4096 <= p <= 140737488355328)%Z.
Hypothesis Ap : (p mod 4 = 0)%Z.
Hypothesis Rj : (0 <= j0 < v)%Z.
Hypothesis Rv : (v <= 256)%Z.
Hypothesis SOK0 : store_ok SEGS M0 (Z_to_bv 64 (p + 4 * j0)) (Z.to_nat (4 * (v - j0))) = true.

Definition qinv (Mi : word -> option byte) : Prop :=
  mem_grows M0 Mi /\ forall x : word, ~ (p + 4 * j0 <= u x < p + 4 * v)%Z -> Mi x = M0 x.

Lemma qinv_refl : qinv M0.
Proof. split; [apply mem_grows_refl | reflexivity]. Qed.
Lemma qinv_step : forall Mi Mi' j, (j0 <= j < v)%Z -> qinv Mi -> mframe [((p + 4 * j)%Z, 4%Z)] Mi Mi' -> qinv Mi'.
Proof.
  intros Mi Mi' j Hj [G F] [G' F']. split; [exact (mem_grows_trans _ _ _ G G')|].
  intros x Hx. rewrite F'; [exact (F x Hx)|]. intros c [<- | []]. unfold incell. cbn [fst snd]. lia.
Qed.
Lemma qinv_step0 : forall Mi Mi', qinv Mi -> mframe [] Mi Mi' -> qinv Mi'.
Proof.
  intros Mi Mi' [G F] [G' F']. split; [exact (mem_grows_trans _ _ _ G G')|].
  intros x Hx. rewrite F'; [exact (F x Hx)|]. intros c [].
Qed.
Lemma qcell_sok : forall Mi j, (j0 <= j < v)%Z -> qinv Mi -> store_ok SEGS Mi (Z_to_bv 64 (p + 4 * j)) 4 = true.
Proof.
  intros Mi j Hj [G _]. apply (reg_sok SEGS M0 Mi (p + 4 * j0) _ (p + 4 * j) 4 G SOK0); rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

(* [comment removed for export] *)
Definition aregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 9 = Z_to_bv 64 p /\ getr regs 10 = Z_to_bv 64 (p + 4 * j) /\ getr regs 11 = Z_to_bv 64 (p + 4 * j) /\ getr regs 21 = Z_to_bv 64 1 /\
  getr regs 23 = Z_to_bv 64 v /\ getr regs 24 = Z_to_bv 64 1 /\ getr regs 25 = Z_to_bv 64 j.

Lemma qfa_loop : forall (n : nat) j regs Mi, (v - j <= Z.of_nat n)%Z -> (j0 <= j < v)%Z -> qinv Mi -> aregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 QFA_HEAD) Mi rom) (mkst regs' (Z_to_bv 64 QFA_EXIT) Mi' rom)
    /\ qinv Mi' /\ regs_agree (fun r => In r [10; 11; 12; 13; 25]%list) regs regs'.
Proof.
  unfold QFA_HEAD, QFA_EXIT. induction n as [|n IH]; intros j regs Mi Hn Hj QI LR; [lia|].
  destruct LR as (H9 & H10 & H11 & H21 & H23 & H24 & H25).
  assert (HYP : qa_hyps p j v) by (unfold qa_hyps; repeat split; first [assumption | lia]).
  destruct (qa_1dec4 rom p j v HYP fx regs Mi (qcell_sok Mi j Hj QI) H9 H10 H11 H21 H23 H24 H25) as (r1 & m1 & RUN1 & FR1 & E10 & E11 & E13 & E25 & AG1).
  pose proof (qinv_step Mi m1 j Hj QI FR1) as QI1.
  destruct (Z_lt_ge_dec (j + 1) v) as [LT|GE].
  - destruct (qa_1def4t rom p j v HYP fx r1 m1 ltac:(ex_br) ltac:(qf_get) E10 E11 E13 ltac:(qf_get) ltac:(qf_get) ltac:(qf_get) E25) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (qinv_step0 m1 m2 QI1 FR2) as QI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) QI2) as (r3 & m3 & RUN3 & QI3 & AG3).
    { unfold aregs. repeat split; qf_get. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact QI3 | ra_chain].
  - destruct (qa_1def4f rom p j v HYP fx r1 m1 ltac:(ex_br) ltac:(qf_get) E10 E11 E13 ltac:(qf_get) ltac:(qf_get) ltac:(qf_get) E25) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (qinv_step0 m1 m2 QI1 FR2) as QI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact QI2 | ra_chain].
Qed.

(* [comment removed for export] *)
Hypothesis V256 : v = 256%Z.
Definition bregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 9 = Z_to_bv 64 p /\ getr regs 10 = Z_to_bv 64 1 /\ getr regs 11 = Z_to_bv 64 (p + 4 * j) /\ getr regs 12 = Z_to_bv 64 256 /\
  getr regs 13 = Z_to_bv 64 (p + 4 * j) /\ getr regs 21 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 j.

Lemma qfb_loop : forall (n : nat) j regs Mi, (v - j <= Z.of_nat n)%Z -> (j0 <= j < v)%Z -> qinv Mi -> bregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 QFB_HEAD) Mi rom) (mkst regs' (Z_to_bv 64 QFB_EXIT) Mi' rom)
    /\ qinv Mi' /\ regs_agree (fun r => In r [11; 13; 14; 15; 23]%list) regs regs'.
Proof.
  unfold QFB_HEAD, QFB_EXIT. induction n as [|n IH]; intros j regs Mi Hn Hj QI LR; [lia|].
  destruct LR as (H9 & H10 & H11 & H12 & H13 & H21 & H23).
  assert (HYP : qb_hyps p j) by (unfold qb_hyps; repeat split; first [assumption | lia]).
  destruct (qb_1dfd8 rom p j HYP fx regs Mi (qcell_sok Mi j Hj QI) H9 H10 H11 H12 H13 H21 H23) as (r1 & m1 & RUN1 & FR1 & E11 & E13 & E15 & E23 & AG1).
  pose proof (qinv_step Mi m1 j Hj QI FR1) as QI1.
  destruct (Z_lt_ge_dec (j + 1) v) as [LT|GE].
  - destruct (qb_1e008t rom p j HYP fx r1 m1 ltac:(ex_br) ltac:(qf_get) ltac:(qf_get) E11 ltac:(qf_get) E13 E15 ltac:(qf_get) E23) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (qinv_step0 m1 m2 QI1 FR2) as QI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) QI2) as (r3 & m3 & RUN3 & QI3 & AG3).
    { unfold bregs. repeat split; qf_get. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact QI3 | ra_chain].
  - destruct (qb_1e008f rom p j HYP fx r1 m1 ltac:(ex_br) ltac:(qf_get) ltac:(qf_get) E11 ltac:(qf_get) E13 E15 ltac:(qf_get) E23) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (qinv_step0 m1 m2 QI1 FR2) as QI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact QI2 | ra_chain].
Qed.
End QFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QFillW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma qf_flag : forall p, (0 < p < 2 ^ 64)%Z -> alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p)) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. intros p Hp. rewrite dl_sltu0 by exact Hp. apply bv_eq. reflexivity. Qed.

Lemma qfillA_hop : forall (fx : FPState) C A Ar M md regs (p n j0 j1 a s : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (s <= c_top C)%Z ->
  live A (Z_to_bv 64 p) = Some n -> live Ar (Z_to_bv 64 p) = None -> live (c_A0 C) (Z_to_bv 64 p) = None -> (0 <= p < 2 ^ 64)%Z ->
  ((0 <=? j0) && (j0 <? j1) && (j1 <=? 256) && (4 * j1 <=? n))%Z%bool = true -> a = (p + 4 * j0)%Z ->
  getr regs 9 = Z_to_bv 64 p -> getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 a ->
  getr regs 21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p) -> getr regs 23 = Z_to_bv 64 j1 ->
  getr regs 24 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p)) (Z_to_bv 64 1) -> getr regs 25 = Z_to_bv 64 j0 ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' ->
      regs_agree (fun r => In r [10; 11; 12; 13; 25]%bv) regs regs' -> (forall x : word, ~ (p <= u x < p + n)%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 QFA_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 QFA_HEAD) M al_rom) md) S.
Proof.
  intros fx C A Ar M md regs p n j0 j1 a s S CK HW SUB Hs L LR L0 Rp HB -> H9 H10 H11 H21 H23 H24 H25 HC.
  apply andb_true_iff in HB as [HB B4]. apply andb_true_iff in HB as [HB B3]. apply andb_true_iff in HB as [B1 B2].
  apply Z.leb_le in B1, B3, B4. apply Z.ltb_lt in B2.
  destruct (exW_blk_rng C A M md p n CK HW L Rp ltac:(lia)) as (G1 & G2 & G3).
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOK : store_ok SEGS M (Z_to_bv 64 (p + 4 * j0)) (Z.to_nat (4 * (j1 - j0))) = true).
  { apply (exW_sok_blk SEGS C A M md p n (p + 4 * j0) (Z.to_nat (4 * (j1 - j0))) p16_segs CK HW L); [lia | lia | lia | rewrite Z2Nat.id by lia; lia]. }
  rewrite dl_sltu0 in H21 by lia. rewrite qf_flag in H24 by lia.
  destruct (qfa_loop (fx := fx) al_rom p j0 j1 M ltac:(lia) (mod16_mod4 _ ALp) ltac:(lia) B3 SOK (Z.to_nat (j1 - j0)) j0 regs M ltac:(lia) ltac:(lia)
              (qinv_refl p j0 j1 M)) as (r' & m' & Hms & [GRW FRM] & AGR).
  { unfold aregs. repeat split; assumption. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact Hms |].
  assert (FRM' : forall x : word, ~ (p <= u x < p + n)%Z -> m' x = M x) by (intros x Hx; apply FRM; lia).
  destruct (exW_framed C A Ar M md m' s p n p (p + n) CK HW SUB Hs GRW FRM' L LR L0 Rp ltac:(lia) ltac:(lia)) as [HW' PM'].
  exact (HC r' m' HW' PM' AGR FRM').
Qed.

Lemma qfillB_hop : forall (fx : FPState) C A Ar M md regs (p n j0 a s : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (s <= c_top C)%Z ->
  live A (Z_to_bv 64 p) = Some n -> live Ar (Z_to_bv 64 p) = None -> live (c_A0 C) (Z_to_bv 64 p) = None -> (0 <= p < 2 ^ 64)%Z ->
  ((0 <=? j0) && (j0 <? 256) && (1024 <=? n))%Z%bool = true -> a = (p + 4 * j0)%Z ->
  getr regs 9 = Z_to_bv 64 p -> getr regs 10 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p)) (Z_to_bv 64 1) ->
  getr regs 11 = Z_to_bv 64 a -> getr regs 12 = Z_to_bv 64 256 -> getr regs 13 = Z_to_bv 64 a ->
  getr regs 21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 p) -> getr regs 23 = Z_to_bv 64 j0 ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' ->
      regs_agree (fun r => In r [11; 13; 14; 15; 23]%bv) regs regs' -> (forall x : word, ~ (p <= u x < p + n)%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 QFB_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 QFB_HEAD) M al_rom) md) S.
Proof.
  intros fx C A Ar M md regs p n j0 a s S CK HW SUB Hs L LR L0 Rp HB -> H9 H10 H11 H12 H13 H21 H23 HC.
  apply andb_true_iff in HB as [HB B3]. apply andb_true_iff in HB as [B1 B2].
  apply Z.leb_le in B1, B3. apply Z.ltb_lt in B2.
  destruct (exW_blk_rng C A M md p n CK HW L Rp ltac:(lia)) as (G1 & G2 & G3).
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOK : store_ok SEGS M (Z_to_bv 64 (p + 4 * j0)) (Z.to_nat (4 * (256 - j0))) = true).
  { apply (exW_sok_blk SEGS C A M md p n (p + 4 * j0) (Z.to_nat (4 * (256 - j0))) p16_segs CK HW L); [lia | lia | lia | rewrite Z2Nat.id by lia; lia]. }
  rewrite dl_sltu0 in H21 by lia. rewrite qf_flag in H10 by lia.
  destruct (qfb_loop (fx := fx) al_rom p j0 256 M ltac:(lia) (mod16_mod4 _ ALp) ltac:(lia) ltac:(lia) SOK eq_refl (Z.to_nat (256 - j0)) j0 regs M ltac:(lia) ltac:(lia)
              (qinv_refl p j0 256 M)) as (r' & m' & Hms & [GRW FRM] & AGR).
  { unfold bregs. repeat split; assumption. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact Hms |].
  assert (FRM' : forall x : word, ~ (p <= u x < p + n)%Z -> m' x = M x) by (intros x Hx; apply FRM; lia).
  destruct (exW_framed C A Ar M md m' s p n p (p + n) CK HW SUB Hs GRW FRM' L LR L0 Rp ltac:(lia) ltac:(lia)) as [HW' PM'].
  exact (HC r' m' HW' PM' AGR FRM').
Qed.
End QFillW.
End V15LeptQFill.
