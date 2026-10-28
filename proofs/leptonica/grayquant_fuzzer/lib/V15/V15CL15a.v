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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL14a.
Module V15LeptDithErr.
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
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL14a.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.
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

Definition STOPS : list Z := [87484]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_RETERR : word := 87484%bv.
Lemma PC_RETERR_eq : Z_to_bv 64 87484 = PC_RETERR. Proof. apply bv_eq; reflexivity. Qed.
Lemma str_dith_msg_d : str16 70751 27. Proof. str16_tac. Qed.
Lemma str_proc_pixDitherToBinary : str16 70578 17. Proof. str16_tac. Qed.

Theorem pixDitherToBinary_d_W : pixDitherToBinary_d_contract.
Proof.
  unfold pixDitherToBinary_d_contract, dither_d_contract, PC_pixDitherToBinary.
  intros fx C A0 m0 md r0 s pixs w h d cm data ret S CK HW0 H2 Hs16 Hlo0 Hhi H1 Hret H10 PXs NEd Lpixs_a0 HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (Hlo : (c_top C - LSTK + 32 <= s)%Z) by (unfold LSF in Hlo0; lia).
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
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_d _ WFs) as Rd. cbn [p_d hdv] in Rd.
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lpixs_a0) as (_ & ALpixs & _). rewrite u_Z2bv in ALpixs by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 32 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) RRpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  pose proof (PIX_rd_d SEGS _ _ _ PXs) as Cd. cbn [p_d hdv] in Cd.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 32) (Z.to_nat 32) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 32 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430112 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-32)) 32 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 8) 4 (EVar 35); KRange (EVar 35) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adriveS 2000%nat 6000%nat STOPS (SCR [true] [] []) FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 32 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 Q1w_0.
  (* [comment removed for export] *)
  rewrite PC_RETERR_eq.
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 70751 70578 27 17 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF in *; lia) Hhi (eq_trans Q1w_0 HRA) Hret Q10_0 Q11_0 Q12_0 str_dith_msg_d str_proc_pixDitherToBinary) end.
  intros m1 r1 HW1 OUT0 GRW0 CSx0 A10_0.
  apply (HC m1 r1 HW1).
  - eapply cs_kept_trans; [|exact CSx0].
    lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT0); unfold LSF in *; lia.
  - exact A10_0.
Qed.

Lemma str_proc_pixDitherTo2bpp : str16 68707 15. Proof. str16_tac. Qed.

Theorem pixDitherTo2bpp_d_W : pixDitherTo2bpp_d_contract.
Proof.
  unfold pixDitherTo2bpp_d_contract, dither_d_contract, PC_pixDitherTo2bpp.
  intros fx C A0 m0 md r0 s pixs w h d cm data ret S CK HW0 H2 Hs16 Hlo0 Hhi H1 Hret H10 PXs NEd Lpixs_a0 HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (Hlo : (c_top C - LSTK + 32 <= s)%Z) by (unfold LSF in Hlo0; lia).
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
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_d _ WFs) as Rd. cbn [p_d hdv] in Rd.
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lpixs_a0) as (_ & ALpixs & _). rewrite u_Z2bv in ALpixs by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 32 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) RRpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  pose proof (PIX_rd_d SEGS _ _ _ PXs) as Cd. cbn [p_d hdv] in Cd.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 32) (Z.to_nat 32) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 32 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430112 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-32)) 32 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 8) 4 (EVar 35); KRange (EVar 35) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; d; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adriveS 2000%nat 6000%nat STOPS (SCR [true] [] []) FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 32 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 Q1w_0.
  (* [comment removed for export] *)
  rewrite PC_RETERR_eq.
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 70751 68707 27 15 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF in *; lia) Hhi (eq_trans Q1w_0 HRA) Hret Q10_0 Q11_0 Q12_0 str_dith_msg_d str_proc_pixDitherTo2bpp) end.
  intros m1 r1 HW1 OUT0 GRW0 CSx0 A10_0.
  apply (HC m1 r1 HW1).
  - eapply cs_kept_trans; [|exact CSx0].
    lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT0); unfold LSF in *; lia.
  - exact A10_0.
Qed.

End Chain.
End V15LeptDithErr.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopyA.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL9a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixDestroyK.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Module V15LeptOwn.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptStderr.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL9a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixDestroyK.
Import V15CL14a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)









Import V15CL7a.V15LeptErr. Import V15CL7a.V15LeptDestroyNull.

Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL9a.V15LeptPixDestroy.


Import V15CL14a.V15LeptDither_iface.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Own.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pblk (pix data cd ad : Z) (q : word) : Prop :=
  q = Z_to_bv 64 pix \/ q = Z_to_bv 64 data \/ (cd <> 0%Z /\ (q = Z_to_bv 64 cd \/ q = Z_to_bv 64 ad)).

Definition cmf (kd kna kn : Z) : Prop := (kd = 1 \/ kd = 2 \/ kd = 4 \/ kd = 8)%Z /\ kna = (2 ^ kd)%Z /\ (1 <= kn <= kna)%Z.

Definition pown (C : lctx) (X Ak : AS) (mk : word -> option byte) (pix w h d cd data ad kd kna kn : Z) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (pix mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pix <> data /\
  (0 < 4 * (wpl_of w d * h))%Z /\ PIXat mk pix (hdv w h d cd data) /\
  live Ak (Z_to_bv 64 pix) = Some 64%Z /\ live Ak (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
  (forall q, pblk pix data cd ad q -> live X q = None /\ live (c_A0 C) q = None) /\
  (cd = 0%Z \/ (cmf kd kna kn /\ (4096 <= cd)%Z /\ (cd + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= ad)%Z /\ (ad + 4 * kna <= alloc_top (c_vm C))%Z /\
       cd <> ad /\ cd <> pix /\ cd <> data /\ ad <> pix /\ ad <> data /\
       live Ak (Z_to_bv 64 cd) = Some 24%Z /\ live Ak (Z_to_bv 64 ad) = Some (4 * kna)%Z /\
       CMAPat mk cd (CMAPV ad kd kna kn 0))).

Lemma pblk_dec : forall pix data cd ad q, pblk pix data cd ad q \/ ~ pblk pix data cd ad q.
Proof.
  intros pix data cd ad q. unfold pblk.
  destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [E1|N1]; [left; left; exact E1|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [E2|N2]; [left; right; left; exact E2|].
  destruct (Z.eq_dec cd 0) as [E0|N0]; [right; intros [X|[X|[X _]]]; contradiction|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [E3|N3]; [left; right; right; split; [exact N0 | left; exact E3]|].
  destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [E4|N4]; [left; right; right; split; [exact N0 | right; exact E4]|].
  right. intros [X|[X|[_ [X|X]]]]; contradiction.
Qed.

Lemma pixt_new_pown : forall C A A' m' pix w h d cd data cv, pixt_new C A A' m' pix w h d cd data cv -> (0 < 4 * (wpl_of w d * h))%Z ->
  exists ad, pown C A A' m' pix w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv) /\ (forall q, ~ pblk pix data cd ad q -> live A' q = live A q).
Proof.
  intros C A A' m' pix w h d cd data cv (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR) Rpos.
  destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)].
  - exists 0%Z. split.
    + unfold pown. do 11 (split; [assumption|]). split; [| left; exact CD0].
      intros q [-> | [-> | [NZ _]]]; [split; assumption | split; assumption | contradiction].
    + intros q NB. apply LEQ; intros ->; apply NB; unfold pblk; auto.
  - exists ad. split.
    + unfold pown. do 11 (split; [assumption|]). split.
      * intros q [-> | [-> | [_ [-> | ->]]]]; split; assumption.
      * right. destruct CMOKc as (D & NA & N & _). split; [split; [exact D | split; [exact NA | exact N]]|]. do 11 (split; [assumption|]). exact CM4.
    + intros q NB. apply LEQ; intros ->; apply NB; unfold pblk; auto; right; right; (split; [lia | auto]).
Qed.

Lemma pown_keep : forall C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, pblk pix data cd ad q -> live Ak' q = live Ak q) -> (forall q, pblk pix data cd ad q -> live Ax q = live Ak q) -> LIVK Ax mk mk' ->
  pown C X Ak' mk' pix w h d cd data ad kd kna kn.
Proof.
  intros C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) EQ EQx LK.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold pown. do 8 (split; [assumption|]).
  assert (Lpx : live Ax (Z_to_bv 64 pix) = Some 64%Z) by (rewrite EQx by (left; reflexivity); exact Lp).
  split; [apply (PIXat_frame mk); [exact PX | intros x Hx; exact (LIVK_at Ax mk mk' pix 64 x LK Lpx ltac:(lia) ltac:(lia) Hx)]|].
  split; [rewrite EQ by (left; reflexivity); exact Lp|]. split; [rewrite EQ by (right; left; reflexivity); exact Ld|]. split; [exact FR|].
  destruct CMR as [CD0 | (CF & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
  assert (Lcdx : live Ax (Z_to_bv 64 cd) = Some 24%Z) by (rewrite EQx by (right; right; split; [lia | left; reflexivity]); exact Lcd).
  do 10 (split; [assumption|]). split; [rewrite EQ by (right; right; split; [lia | left; reflexivity]); exact Lcd|].
  split; [rewrite EQ by (right; right; split; [lia | right; reflexivity]); exact Lad|].
  apply (CMAPat_frame mk); [exact CM | intros x Hx; exact (LIVK_at Ax mk mk' cd 24 x LK Lcdx ltac:(lia) ltac:(lia) Hx)].
Qed.

Lemma pown_sub : forall C X X' Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> sub_live X' X -> pown C X' Ak mk pix w h d cd data ad kd kna kn.
Proof.
  intros C X X' Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) SUB.
  unfold pown. do 11 (split; [assumption|]). split; [| exact CMR].
  intros q B. destruct (FR q B) as [F1 F2]. split; [| exact F2].
  destruct (live X' q) as [k|] eqn:E; [apply SUB in E; congruence | reflexivity].
Qed.

Lemma pown_live : forall C X Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> forall q, pblk pix data cd ad q -> exists k, live Ak q = Some k.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR) q B.
  destruct B as [-> | [-> | [NZ B]]]; [eexists; exact Lp | eexists; exact Ld |].
  destruct CMR as [CD0 | (CF & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [contradiction|].
  destruct B as [-> | ->]; eexists; eassumption.
Qed.

(* [comment removed for export] *)
Lemma pown_disj : forall C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2,
  pown C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 -> pown C X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 -> sub_live Ak1 X2 ->
  forall q, pblk p1 data1 cd1 ad1 q -> ~ pblk p2 data2 cd2 ad2 q.
Proof.
  intros C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 O1 O2 SUB q B1 B2.
  destruct (pown_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ O1 q B1) as [k Lk]. apply SUB in Lk.
  destruct O2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _). destruct (FR q B2) as [F _]. congruence.
Qed.

Lemma pown_cm_facts : forall C X Ak mk pix w h d cd data ad kd kna kn,
  pown C X Ak mk pix w h d cd data ad kd kna kn -> cm_facts Ak mk cd (CMAPV ad kd kna kn 0).
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
  destruct CMR as [CD0 | ((D & NA & N) & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
  split; [exact CM|]. split; [unfold cmap_ok; cbn [c_d c_nalloc c_n c_arr]; repeat split; try assumption; lia|].
  split; [exact Lcd | exact Lad].
Qed.

(* [comment removed for export] *)
Definition oown (C : lctx) (X Ak : AS) (mk : word -> option byte) (pix w h d cd data ad kd kna kn : Z) : Prop :=
  pix = 0%Z \/ pown C X Ak mk pix w h d cd data ad kd kna kn.
Definition oblk (pix data cd ad : Z) (q : word) : Prop := pix <> 0%Z /\ pblk pix data cd ad q.

Lemma oblk_dec : forall pix data cd ad q, oblk pix data cd ad q \/ ~ oblk pix data cd ad q.
Proof.
  intros pix data cd ad q. unfold oblk. destruct (Z.eq_dec pix 0) as [E|N]; [right; intros [X _]; contradiction|].
  destruct (pblk_dec pix data cd ad q) as [B|NB]; [left; split; assumption | right; intros [_ X]; contradiction].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sp_slot_al8 : forall sp k, (sp mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((sp - k) mod 8 = 0)%Z.
Proof.
  intros sp k H1 H2. apply Zmod_divides in H1 as [c ->]; [|lia]. apply Zmod_divides in H2 as [e ->]; [|lia].
  replace (16 * c - 8 * e)%Z with ((2 * c - e) * 8)%Z by ring. apply Z_mod_mult.
Qed.


Lemma raster_pos : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (0 < 4 * (wpl_of w d * h))%Z.
Proof.
  intros w h d (DV & Hw2 & Hh2 & Hsz) Hw Hh. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwr.
  assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.

Lemma pixDestroy_opt_W : forall C X A m md regs (s pp pix w h d cd data ad kd kna kn : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  oown C X A m pix w h d cd data ad kd kna kn ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall q, oblk pix data cd ad q -> live A' q = None) -> (forall q, ~ oblk pix data cd ad q -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' -> (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x170a4 : word) m al_rom) md) S.
Proof.
  intros C X A m md regs s pp pix w h d cd data ad kd kna kn ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALpp H10 Rpp OO HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in *.
  destruct OO as [P0 | OWN].
  - subst pix.
    replace (0x170a4 : word) with (Z_to_bv 64 0x170a4) by (apply bv_eq; reflexivity).
    apply (pixDestroy_null_W fx C A m md regs s pp ret S CK HW H2 ltac:(lia) Hpp Hpphi ALpp H1 Hret H10 Rpp).
    intros m' r' HW' CS' PM' OUT'. rewrite <- (with_vmmaps_same md). apply (HK A m' (m_vmmaps md) r').
    + rewrite with_vmmaps_same. exact HW'.
    + exact CS'.
    + intros q [NZ0 _]. contradiction.
    + intros q _. reflexivity.
    + eapply POSTM_mono; [|exact PM']. lia.
    + intros a Ha. apply OUT'. lia.
    + apply roomtr_refl; lia.
  - pose proof OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p]. destruct (FR _ (or_intror (or_introl eq_refl))) as [_ L0d].
    assert (HCM : cd = 0%Z \/ (CMAPat m cd (CMAPV ad kd kna kn 0) /\ live A (Z_to_bv 64 cd) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr (CMAPV ad kd kna kn 0))) = Some (4 * kna)%Z /\
                live (c_A0 C) (Z_to_bv 64 cd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr (CMAPV ad kd kna kn 0))) = None /\
                cd <> c_arr (CMAPV ad kd kna kn 0) /\ cd <> pix /\ c_arr (CMAPV ad kd kna kn 0) <> pix /\ p_data (hdv w h d cd data) <> cd /\
                p_data (hdv w h d cd data) <> c_arr (CMAPV ad kd kna kn 0) /\ (0 < 4 * kna)%Z)).
    { destruct CMR as [CD0 | ((D & NA & N) & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lcd & Lad & CM)]; [left; exact CD0 | right].
      assert (NZ : cd <> 0%Z) by lia.
      destruct (FR (Z_to_bv 64 cd) (or_intror (or_intror (conj NZ (or_introl eq_refl))))) as [_ L0cd].
      destruct (FR (Z_to_bv 64 ad) (or_intror (or_intror (conj NZ (or_intror eq_refl))))) as [_ L0ad].
      cbn [c_arr p_data hdv]. repeat (split; [first [assumption | congruence | lia]|]).
      assert (0 < 2 ^ kd)%Z by (apply Z.pow_pos_nonneg; lia). lia. }
    apply (pixDestroy_keep_W C A m md regs s pp pix cd (4 * kna) (4 * (wpl_of w d * h)) (hdv w h d cd data) (CMAPV ad kd kna kn 0) ret S CK HW H2 Hs16
             ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi H1 Hret H4 ALpp H10 Rpp PX eq_refl eq_refl eq_refl Lp L0p Ld L0d Rpos ltac:(cbn [p_data hdv]; congruence) HCM).
    intros A' m' vm' r' HW' CS' (P1 & P2 & P3 & P4) PM' R0' OUT' RT'. cbn [p_data hdv c_arr] in P2, P3, P4.
    apply (HK A' m' vm' r' HW' CS').
    + intros q [_ [-> | [-> | [NZ [-> | ->]]]]]; [exact P1 | apply P2; lia | exact (proj1 (P3 NZ)) | exact (proj2 (P3 NZ))].
    + intros q NB. apply P4.
      * intros ->. apply NB. split; [lia | left; reflexivity].
      * intros _ ->. apply NB. split; [lia | right; left; reflexivity].
      * intros NZ. split; intros ->; apply NB; (split; [lia|]); right; right; (split; [exact NZ|]); [left | right]; reflexivity.
    + exact PM'.
    + exact OUT'.
    + exact RT'.
Qed.

Lemma oown_range : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn -> (0 <= pix < 2 ^ 64)%Z.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn [-> | (Gp & TOPp & _)]; [lia|].
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. lia.
Qed.

Lemma oown_keep : forall C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn,
  oown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, oblk pix data cd ad q -> live Ak' q = live Ak q) -> (forall q, oblk pix data cd ad q -> live Ax q = live Ak q) -> LIVK Ax mk mk' ->
  oown C X Ak' mk' pix w h d cd data ad kd kna kn.
Proof.
  intros C X Ak Ak' Ax mk mk' pix w h d cd data ad kd kna kn [P0 | OWN] EQ EQx LK; [left; exact P0 | right].
  assert (NZ : pix <> 0%Z) by (destruct OWN as (Gp & _); lia).
  apply (pown_keep C X Ak Ak' Ax mk mk'); [exact OWN | intros q B; apply EQ; split; assumption | intros q B; apply EQx; split; assumption | exact LK].
Qed.

(* [comment removed for export] *)
Lemma oblk_fresh : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn ->
  forall q, oblk pix data cd ad q -> live X q = None.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn [P0 | OWN] q [NZ B]; [contradiction|].
  destruct OWN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _). exact (proj1 (FR q B)).
Qed.

Lemma oown_sub_live : forall C X Ak mk pix w h d cd data ad kd kna kn, oown C X Ak mk pix w h d cd data ad kd kna kn ->
  (forall q, ~ oblk pix data cd ad q -> live Ak q = live X q) -> sub_live X Ak.
Proof.
  intros C X Ak mk pix w h d cd data ad kd kna kn OO LEQ q k Lq.
  destruct (oblk_dec pix data cd ad q) as [B|NB]; [rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OO q B) in Lq; discriminate | rewrite (LEQ q NB); exact Lq].
Qed.

Lemma oown_sub : forall C X X' Ak mk pix w h d cd data ad kd kna kn,
  oown C X Ak mk pix w h d cd data ad kd kna kn -> sub_live X' X -> oown C X' Ak mk pix w h d cd data ad kd kna kn.
Proof. intros C X X' Ak mk pix w h d cd data ad kd kna kn [P0 | OWN] SUB; [left; exact P0 | right; exact (pown_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN SUB)]. Qed.

(* [comment removed for export] *)
Lemma oown_disj : forall C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2,
  oown C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 -> oown C X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 -> sub_live Ak1 X2 ->
  forall q, oblk p1 data1 cd1 ad1 q -> ~ oblk p2 data2 cd2 ad2 q.
Proof.
  intros C X1 Ak1 mk1 p1 w1 h1 d1 cd1 data1 ad1 kd1 kna1 kn1 X2 Ak2 mk2 p2 w2 h2 d2 cd2 data2 ad2 kd2 kna2 kn2 O1 O2 SUB q [NZ1 B1] B2.
  destruct O1 as [P0 | OWN1]; [contradiction|].
  destruct (pown_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWN1 q B1) as [k Lk]. apply SUB in Lk.
  rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ O2 q B2) in Lk. discriminate.
Qed.

(* [comment removed for export] *)

End Own.
End V15LeptOwn.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require MallocShape.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15_code_gqD.
Module V15LeptPixDestroyRc2.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocShape.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15_code_gqD.
Import V15CL14a.
(* [comment removed for export] *)









Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Lemma pxd2_run : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pix mod 16 = 0)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
    PIXat m pix v -> p_rc v = 2%Z -> (pix + 64 <= s - 32 \/ pp + 8 <= pix)%Z -> (4096 <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x170a4 : word) m rom)
                  (mkst regs' ret
                        (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                                (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                                (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pp pix v ret Hs Hpp Hpp64 Hal ALp Hret SOK SOKp SOKpp Rpp PX RC DJ Hpix H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    eexists. split.
    - zv F_16fa0 D_16fa0 (Z_to_bv 64 (s - 32)).
      stepST F_16fa4 D_16fa4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16fa8 D_16fa8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16fac D_16fac (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_16fb0 D_16fb0 ltac:(condZ).
      stepiv F_16fb4 D_16fb4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALp; reflexivity).
      stepb_ft F_16fb8 D_16fb8 ltac:(condZ).
      stepLD F_16fbc D_16fbc (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_16fc0 D_16fc0 ltac:(condZ).
      stepiv F_16fc4 D_16fc4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity).
      stepb_ft F_16fc8 D_16fc8 ltac:(condZ).
      zv F_16fcc D_16fcc (Z_to_bv 64 (pix + 20)).
      sn F_16fd0 D_16fd0.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 2) (Z_to_bv 64 2) F_16fd4 eq_refl D_16fd4);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; repeat rdn_peel1; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (2 + 18446744073709551615)%Z) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 2) by lia.
      sn F_16fd8 D_16fd8.
      stepb_tk F_16fdc D_16fdc ltac:(condZ).
      stepST F_17028 D_17028 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOKpp).
      sn F_1702c D_1702c.
      stepLD8 F_17068 D_17068 ret.
      stepLD8 F_1706c D_1706c (getr regs 8).
      stepLD8 F_17070 D_17070 (getr regs 9).
      zv F_17074 D_17074 (Z_to_bv 64 s).
      stepret F_17078 D_17078 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Section Rc2W.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Theorem pixDestroy_rc2s_W : forall (fx : FPState) C A m md regs (s pp pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PXD2_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 2%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     POSTM C A (pp + 8) (wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) m' ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixDestroy) m al_rom) md) S.
Proof.
  unfold PC_pixDestroy, PXD2_STACK.
  intros fx C A m md regs s pp pix v ret S CK HW H2 Hs16 Hlo Hpp Hhi ALpp H1 Hret H10 Rpp PX RC L L0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. unfold ALLOC_STACK in *.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW L ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (blk_sok C A m md pix 64 CK HW L ltac:(lia) ltac:(lia) ltac:(lia)) as SOKp.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKf.
  pose proof (W_sok_win C A m md pp 8 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKpp.
  destruct (pxd2_run al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp ALpp Hret SOKf SOKp SOKpp Rpp PX RC ltac:(lia) ltac:(lia) H2 H1 H10)
    as (regs' & RUN & Q2 & Q8 & Q9 & AG).
  replace (Z_to_bv 64 0x170a4) with (0x170a4 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  assert (LEN8 : forall w0 : word, Z.of_nat (length (word_to_le_bytes 8 w0)) = 8%Z) by (intros w0; rewrite length_N_to_le_bytes; reflexivity).
  assert (LEN4 : forall w0 : word, Z.of_nat (length (word_to_le_bytes 4 w0)) = 4%Z) by (intros w0; rewrite length_N_to_le_bytes; reflexivity).
  apply HK.
  - (* [comment removed for export] *)
    apply (W_store_win C A _ md _ _ CK); [| rewrite u_Z2bv by lia; lia | rewrite u_Z2bv, LEN8 by lia; lia].
    apply (W_store_blk C A _ md (Z_to_bv 64 pix) _ 64 _ CK); [| exact L | exact L0 | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv, LEN4 by lia; lia].
    apply (W_store_win C A _ md _ _ CK); [| rewrite u_Z2bv by lia; lia | rewrite u_Z2bv, LEN8 by lia; lia].
    apply (W_store_win C A _ md _ _ CK); [| rewrite u_Z2bv by lia; lia | rewrite u_Z2bv, LEN8 by lia; lia].
    apply (W_store_win C A _ md _ _ CK); [exact HW | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv, LEN8 by lia; lia].
  - apply cs_kept_intro; first [ (rewrite Q2, H2; reflexivity) | exact Q8 | exact Q9 | (apply AG; notin_list) ].
  - (* [comment removed for export] *)
    rewrite (w2b_Z 4 1) by lia. rewrite (w2b_Z 8 0) by lia.
    assert (EQ : forall x : word, ~ (s - 32 <= u x < s)%Z ->
              wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0) x
              = wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0) x).
    { intros x Hx. apply wbytes_pointwise. apply wbytes_pointwise.
      rewrite !wbytes_outside by (rewrite ?LEN8, ?u_Z2bv by lia; lia). reflexivity. }
    set (mp := wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) in *.
    assert (HWp : W C A mp md).
    { unfold mp. apply (W_store_win C A _ md _ _ CK); [| rewrite u_Z2bv by lia; lia | rewrite u_Z2bv, length_Z_to_le_bytes by lia; lia].
      apply (W_store_blk C A _ md (Z_to_bv 64 pix) _ 64 _ CK HW L L0); [rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv, length_Z_to_le_bytes by lia; lia]. }
    apply (POSTM_mono C A s (pp + 8)); [lia|].
    apply (POSTM_range C A mp md _ (s - 32) s s CK HWp); [| lia | lia | lia].
    intros x Hx. apply EQ. lia.
  - intros a Ha. rewrite !wbytes_outside by (rewrite ?LEN8, ?LEN4, ?u_Z2bv by lia; lia). reflexivity.
Qed.

Theorem pixDestroy_rc2_W : pixDestroy_rc2_contract.
Proof.
  intros fx C A m md regs s pp pix v ret S CK HW H2 Hs16 Hlo Hpp Hhi ALpp H1 Hret H10 Rpp PX RC L L0 HK.
  apply (pixDestroy_rc2s_W fx C A m md regs s pp pix v ret S CK HW H2 Hs16 Hlo Hpp Hhi ALpp H1 Hret H10 Rpp PX RC L L0).
  intros m' regs' HW' CS PM _. exact (HK m' regs' HW' CS PM).
Qed.
End Rc2W.
End V15LeptPixDestroyRc2.
