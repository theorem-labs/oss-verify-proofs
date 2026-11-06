(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.leptonica.grayquant_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecW.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecFP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15LeptBase.
Module O15LeptDestroyNull.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptBase.
(* [comment removed for export] *)









Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O15Pins}.
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
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 93092) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pp ret S CK HW0 H2 Hlo Hpp Hhi0 ALpp H1 Hret H10 Cpp HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LL16] in *. pose proof LSTK_val as LV.
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
  pose proof (exW_canary_ok SEGS 384440 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 384440 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 384440 m0]) (EVar 35) (EVar 32) (exW_canary SEGS 384440 m0) s 32 384440 65536 180224 182064 182216 182064 182216
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 384440 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 63); KAlign (EVar 34) 8; KDisj (SA (EVar 32) (-32)) 32 (SA (EVar 34) 0) 8; KWord (SA (EVar 34) 0) 8 (ELit 0)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pp; exW_canary SEGS 384440 m0] HR.
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
End O15LeptDestroyNull.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15LeptStderr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15_code_150a4_160a4.
Module O15LeptErr.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptStderr.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15_code_150a4_160a4.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Err.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O15Pins}.

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
      msteps SEGS (mkst regs (0x15478 : word) m rom)
                  (mkst regs' (0x153dc : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x15498
      /\ getr regs' 10 = Z_to_bv 64 0x11483 /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_15420 D_15420 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_15424 D_15424 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_15428 D_15428 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_1542c D_1542c.                                                     (* [comment removed for export] *)
      sn F_15430 D_15430.                                                     (* [comment removed for export] *)
      sn F_15434 D_15434.                                                     (* [comment removed for export] *)
      sn F_15438 D_15438.                                                     (* [comment removed for export] *)
      sn F_1543c D_1543c.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x15498 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_15440 D_15440.                                                     (* [comment removed for export] *)
      stepLD8 F_15444 D_15444 ret.                                            (* [comment removed for export] *)
      stepLD8 F_15448 D_15448 s0v.                                            (* [comment removed for export] *)
      zv F_1544c D_1544c (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_15450 D_15450 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x15478 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rep_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x15498) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rep_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x15498) with (0x15498 : word) by (apply bv_eq; reflexivity).
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
      msteps SEGS (mkst regs (0x153a8 : word) m rom)
                  (mkst regs' (0x153dc : word)
                        (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x153c8
      /\ getr regs' 10 = Z_to_bv 64 0x11483 /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 msg
      /\ getr regs' 8 = val
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
  Proof.
    intros regs m s msg proc ret val Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_15350 D_15350 (Z_to_bv 64 (s - 16)).                              (* [comment removed for export] *)
      stepST F_15354 D_15354 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).     (* [comment removed for export] *)
      stepST F_15358 D_15358 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).  (* [comment removed for export] *)
      sn F_1535c D_1535c.                                                     (* [comment removed for export] *)
      sn F_15360 D_15360.                                                     (* [comment removed for export] *)
      sn F_15364 D_15364.                                                     (* [comment removed for export] *)
      sn F_15368 D_15368.                                                     (* [comment removed for export] *)
      sn F_1536c D_1536c.                                                     (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x153c8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Hret R8 R16 H2.
    eexists. split.
    - sn F_15370 D_15370.                                                     (* [comment removed for export] *)
      stepLD8 F_15374 D_15374 ret.                                            (* [comment removed for export] *)
      stepLD8 F_15378 D_15378 s0v.                                            (* [comment removed for export] *)
      zv F_1537c D_1537c (Z_to_bv 64 s).                                      (* [comment removed for export] *)
      stepret F_15380 D_15380 ret ltac:(bveq).                                (* [comment removed for export] *)
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
  realizes SEGS (mkCfg (mkst regs (0x153a8 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s msg proc kmsg kproc ret val S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Smsg Sproc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof Smsg as (_ & _ & Bm & _). pose proof Sproc as (_ & _ & Bp & _).
  destruct (rei_A al_rom regs m s msg proc ret val ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_win C A); [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply (W_store_win C A); [exact CK | exact HW | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  apply (lept_stderr2_W C A M1 md r1 (s - 16) proc msg kproc kmsg (Z_to_bv 64 0x153c8) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           Q10 Q11 Q12 Sproc Smsg).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (rei_B al_rom r2 m2 s ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & P2 & P1 & P10 & P8 & AG3).
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { apply (rdn_after M1 m2 (s - 16 - 3376) (s - 16)); [exact OUT2 | lia | cbn; lia | cbn; lia |]. subst M1. rdn_solve. }
  { exact E2. }
  replace (Z_to_bv 64 0x153c8) with (0x153c8 : word) by (apply bv_eq; reflexivity).
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
End O15LeptErr.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.OL Require LeptBase.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15Kit.
Module O15LeptG.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc.Reloc.
Import O15Kit.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptBase.
(* [comment removed for export] *)








Import O15Kit.O15Reloc. Import O15Kit.O15RelocOL.


Lemma o15_LL : LL16 = @LeptBase.LLG o15_reloc o15_lept.
Proof. reflexivity. Qed.

Definition o15_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @O15Pins AL CL) : @LeptBase.PinsG o15_reloc AL CL :=
  @LeptBase.Build_PinsG o15_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
End O15LeptG.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecT.
Module O15LeptPixClone.
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
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15LeptBase.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
(* [comment removed for export] *)










Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_pixClone : Z := 94848.

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
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LL16] in *. pose proof LSTK_val as LV.
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
  pose proof (exW_kwr_blk2 SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 384440 m0]) (EVar 34) pix 64 p16_segs CK HW0 Lpix_a0 RRpix eq_refl eq_refl) as HKw.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pix 64 CK HW0 Lpix_a0 eq_refl RRpix GLO1) as WAPpix.
  destruct (exW_blk_rng C A0 m0 _ pix 64 CK HW0 Lpix_a0 RRpix eq_refl) as (Gp1 & Gp2 & Gp3).
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpix_a0) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 16) (Z.to_nat 16) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 384440 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 384440 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 384440 m0]) (EVar 35) (EVar 32) (exW_canary SEGS 384440 m0) s 16 384440 65536 180224 182064 182216 182064 182216
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 384440 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-16)) 16 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 20) 4 (ELit 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKw HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pix; exW_canary SEGS 384440 m0] HR.
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
End O15LeptPixClone.
