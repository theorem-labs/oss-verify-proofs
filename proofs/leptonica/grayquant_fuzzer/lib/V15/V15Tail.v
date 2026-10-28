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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL9a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopyA.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixDestroyK.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL14a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL15a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL16a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecT.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
Module V15LeptFuzz.
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
Import V15CL9a.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixDestroyK.
Import V15CL14a.
Import V15CL15a.
Import V15CL16a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr. Import V15CL7a.V15LeptDestroyNull.

Import V15CL8a.V15LeptPixHdr.


Import V15CL9a.V15LeptPixDestroy.

Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.

Import V15CL15a.V15LeptOwn.

Import V15CL16a.V15LeptGq_iface.

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

Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_PIXCOPY : word := 96784%bv.
Lemma PC_PIXCOPY_eq : Z_to_bv 64 96784 = PC_PIXCOPY. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_DESTROY : word := 94372%bv.
Lemma PC_DESTROY_eq : Z_to_bv 64 94372 = PC_DESTROY. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_rg1 : reg := 1%bv. Definition ex_rg8 : reg := 8%bv. Definition ex_rg9 : reg := 9%bv.
Definition ex_r14 : reg := 14%bv. Definition ex_r15 : reg := 15%bv.
Definition ex_r18 : reg := 18%bv. Definition ex_r19 : reg := 19%bv. Definition ex_r20 : reg := 20%bv. Definition ex_r21 : reg := 21%bv. Definition ex_r22 : reg := 22%bv. Definition ex_r23 : reg := 23%bv. Definition ex_r24 : reg := 24%bv. Definition ex_r25 : reg := 25%bv. Definition ex_r26 : reg := 26%bv. Definition ex_r27 : reg := 27%bv. 
(* [comment removed for export] *)
Definition gq_csrest (regs regsE : bvmap 5 word) : Prop :=
  getr regs 18 = getr regsE 18 /\ getr regs 19 = getr regsE 19 /\ getr regs 20 = getr regsE 20 /\ getr regs 21 = getr regsE 21 /\ getr regs 22 = getr regsE 22 /\ getr regs 23 = getr regsE 23 /\ getr regs 24 = getr regsE 24 /\ getr regs 25 = getr regsE 25 /\ getr regs 26 = getr regsE 26 /\ getr regs 27 = getr regsE 27.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS1 : list Z := [96784; 116080; 94372; 86968]%Z.
Lemma round_1 : F1_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_d2bpp <= kR)%Z -> (RB_pixcopy14 + RB_d2bpp <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_d2bpp) (bR - RB_pixcopy14 - RB_d2bpp) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 86968) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 86924) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS1).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1. exW_regfactB BS1 HR ex_r11 Q11_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 Q11_1
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 Q11_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS2 : list Z := [96784; 112068; 94372; 87008]%Z.
Lemma round_2 : F2_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_dbin <= kR)%Z -> (RB_pixcopy14 + RB_dbin <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_dbin) (bR - RB_pixcopy14 - RB_dbin) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 87008) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 86968) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS2).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 I
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS3 : list Z := [96784; 114844; 94372; 87064]%Z.
Lemma round_3 : F3_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_mask <= kR)%Z -> (RB_pixcopy14 + RB_mask <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_mask) (bR - RB_pixcopy14 - RB_mask) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 87064) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 87008) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS3).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r13 Q13_1. exW_regfactB BS1 HR ex_r14 Q14_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 (conj Q11_1 (conj Q12_1 (conj Q13_1 Q14_1)))
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 Q11_1 Q12_1 Q13_1 Q14_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS4 : list Z := [96784; 123164; 94372; 87124]%Z.
Lemma round_4 : F4_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_mask <= kR)%Z -> (RB_pixcopy14 + RB_mask <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_mask) (bR - RB_pixcopy14 - RB_mask) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 87124) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 87064) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS4).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r13 Q13_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 (conj Q11_1 (conj Q12_1 (conj Q13_1 (conj ltac:(apply fr_get_lit; vm_cast_no_check (eq_refl (Some (ELit 18446744069414584320)))) ltac:(apply fr_get_lit; vm_cast_no_check (eq_refl (Some (ELit 18446744069414584320))))))))
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 Q11_1 Q12_1 Q13_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS5 : list Z := [96784; 124628; 94372; 87176]%Z.
Lemma round_5 : F5_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_mask <= kR)%Z -> (RB_pixcopy14 + RB_mask <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_mask) (bR - RB_pixcopy14 - RB_mask) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 87176) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 87124) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS5).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r13 Q13_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 (conj Q11_1 (conj Q12_1 Q13_1))
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 Q11_1 Q12_1 Q13_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS6 : list Z := [96784; 119812; 94372; 87240]%Z.
Lemma round_6 : F6_contract -> forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs w h d cm data : Z) (cv : cmapv) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + RK_thr_gq <= kR)%Z -> (RB_pixcopy14 + RB_thr_gq <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> POSTM C A s m m' -> (forall q, live A' q = live A q) ->
      getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
      aroom A' vm' (kR - RK_pixcopy - RK_thr_gq) (bR - RB_pixcopy14 - RB_thr_gq) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 87240) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 87176) m al_rom) md) S.
Proof.
  intros HF fx C A0 m0 md r0 regsE s pixs w h d cm data cv S FZ CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp PXs HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS6).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h d cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (CMFM0 : cm_facts A0 M0 cm cv) by exact (cmf_sess _ C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 CMF FRs0).
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h d cm data cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldata_a0 CMFM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  unfold TK. intros A1 m1 vm1 r1 HW1 CSx0 PMc0 RES0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct (copy_oown _ C A0 A1 m1 r1 w h d cv HOK Hw1 Hh1 RES0) as (pixc & cdc & datac & adc & A10_0 & OC1 & LEQ0).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1) as RRpixc.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC1 LEQ0) as SUB1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 48 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixc; exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 71) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 CMFM0 RES0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixc; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixc; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r13 Q13_1. exW_regfactB BS1 HR ex_r14 Q14_1. exW_regfactB BS1 HR ex_r15 Q15_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (OCM1 : oown C A0 A1 M1 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A1 A1 m1 M1 _ _ _ _ _ _ _ _ _ _ OC1 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (exT_livk_sess C A1 m1 M1 _ s 48 CK HW1 GLO1 FRs1)).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HF fxk C A0 A1 M1 _ Rc1 (s + OFF1)%Z pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S FZ CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, GQ_STACK_F; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 (conj Q11_1 (conj Q12_1 (conj Q13_1 (conj Q14_1 Q15_1))))
             OCM1 HOK Hw1 Hh1 (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) end end.
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CSx1 PMc1 RES1 RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct (res_oown _ C A1 A2 m2 r2 RES1) as (pr & w' & h' & d' & cdr & datar & adr & kd' & kna' & kn' & A10_1 & OR2 & LEQ1).
  pose proof (oown_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2) as RRpr. pose proof OR2 as ORk.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR2 LEQ1) as SUB12.
  pose proof (sub_live_trans _ _ _ SUB1 SUB12) as SUB2.
  pose proof (oown_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM1 OR2 (sub_live_refl A1)) as DISJ.
  assert (OC2 : oown C A0 A2 m2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv))
    by exact (oown_keep C A0 A1 A2 A1 M1 m2 _ _ _ _ _ _ _ _ _ _ OCM1 (fun q0 B => LEQ1 q0 (DISJ q0 B)) (fun _ _ => eq_refl) (proj2 PMc1)).
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 48 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pr; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 Q11_1 Q12_1 Q13_1 Q14_1 Q15_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 RM1 A10_1 OCM1 RES1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 48) (Z.to_nat 48) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pr; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [pr; exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 48 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 48 [] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose (BSx2 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx2 (EVar 32) s (-40)%Z 8%nat CELLpp.
  clear BSx2.
  pose proof (exT_livk_sess C A2 m2 M2 _ s 48 CK HW2 GLO1 FRs2) as LKs2.
  assert (OCM2 : oown C A0 A2 M2 pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv)) by exact (oown_keep C A0 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OC2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (ORM2 : oown C A1 A2 M2 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A2 A2 A2 m2 M2 _ _ _ _ _ _ _ _ _ _ OR2 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs2).
  assert (PPlo : (s + OFF2 <= s + -40)%Z) by (unfold OFF2; lia). assert (PPhi : (s + -40 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A0 A2 M2 _ Rc2 (s + OFF2) (s + -40) pixc w h d cdc datac adc (c_d cv) (c_nalloc cv) (c_n cv) (Z_to_bv 64 ra) S CK HWs2 Q2_2
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF2, ALLOC_STACK; lia) PPlo PPhi Q1_2 ltac:(red; apply bv_eq; reflexivity) Q4_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_2 CELLpp OCM2) end end.
  intros A3 m3 vm3 r3 HW3 CSx2 DEAD3 LEQd3 PMc2 FRMs2 RTR2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (DISJr : forall q0, oblk pr datar cdr adr q0 -> ~ oblk pixc datac cdc adc q0) by (intros q0 Br Bc; exact (DISJ q0 Bc Br)).
  assert (OR3 : oown C A1 A3 m3 pr w' h' d' cdr datar adr kd' kna' kn')
    by exact (oown_keep C A1 A2 A3 A3 M2 m3 _ _ _ _ _ _ _ _ _ _ ORM2 (fun q0 B => LEQd3 q0 (DISJr q0 B)) (fun q0 B => LEQd3 q0 (DISJr q0 B)) (proj2 PMc2)).
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQd3 q0); [exact (SUB2 _ _ Lq)|]. intros B. rewrite (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OCM2 q0 B) in Lq. discriminate Lq. }
  pose proof (RTR2 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + -40 + 8) s); [lia | exact PMc2]. }
  assert (FRMx2 : FRM C (s + -32) M2 m3).
  { replace (s + -32)%Z with (s + -40 + 8)%Z by lia. exact (proj1 PMc2). }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, (-32)%Z, 0%Z); (EVar 32, OFF2, (-40)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-32) 48 M2 m3 E2 (EVar 32) CK FRMx2 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E2 M2 m3 (EVar 32) s OFF2 (-40) (s + OFF2) (s + -40) FRMs2 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr2 (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 FRs2 CS2 OFF2 CELLpp LKs2 OCM2 PPlo PPhi PMc2 FRMx2 FRMs2 RTR2 RM2 ORM2 OR2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 48) (Z.to_nat 48) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 48 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 48 [] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-48)%Z 8%nat CELLpp.
  clear BSx3.
  pose proof (exT_livk_sess C A3 m3 M3 _ s 48 CK HW3 GLO1 FRs3) as LKs3.
  assert (ORM3 : oown C A1 A3 M3 pr w' h' d' cdr datar adr kd' kna' kn') by exact (oown_keep C A1 A3 A3 A3 m3 M3 _ _ _ _ _ _ _ _ _ _ OR3 (fun _ _ => eq_refl) (fun _ _ => eq_refl) LKs3).
  assert (PPlo : (s + OFF3 <= s + -48)%Z) by (unfold OFF3; lia). assert (PPhi : (s + -48 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_opt_W (fx := fxk) C A1 A3 M3 _ Rc3 (s + OFF3) (s + -48) pr w' h' d' cdr datar adr kd' kna' kn' (Z_to_bv 64 ra) S CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, ALLOC_STACK; lia) PPlo PPhi Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_3 CELLpp ORM3) end end.
  intros A4 m4 vm4 r4 HW4 CSx3 DEAD4 LEQd4 PMc3 FRMs3 RTR3.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQd4 q0); [exact (SUB3 _ _ Lq)|]. intros B. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ ORM3 q0 B) as F1. rewrite (SUB1 _ _ Lq) in F1. discriminate F1. }
  pose proof (RTR3 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; unfold RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pixcopy, RK_cmapcopy, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pixcopy14, RB_cmapcopy, RB_pix14 in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -48 + 8) s); [lia | exact PMc3]. }
  assert (FRMx3 : FRM C (s + -40) M3 m4).
  { replace (s + -40)%Z with (s + -48 + 8)%Z by lia. exact (proj1 PMc3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-40)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-40) 48 M3 m4 E3 (EVar 32) CK FRMx3 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr2 (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 CS3 OFF3 CELLpp LKs3 ORM3 PPlo PPhi PMc3 FRMx3 FRMs3 RTR3 RM3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 48) (Z.to_nat 48) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (exW_canary SEGS 415784 m4) s 48 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 48 [] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (71%nat, pixc); (105%nat, pr); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A4 M4 vm4 RcF FZ HWs4 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)
             (round_live _ C A0 A1 A2 A3 A4 m1 m2 pixc w h d cdc datac adc _ _ _ pr w' h' d' cdr datar adr kd' kna' kn' OC1 LEQ0 ORk LEQ1 DEAD3 LEQd3 DEAD4 LEQd4)
             G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp RM4) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_fuzz_B0 : list Z := [86924]%Z.
Lemma fuzz_B0 : forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 10 = Z_to_bv 64 0 -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  getr regsE 1 = ret -> ret_ok ret -> getr regsE 2 = Z_to_bv 64 s -> getr regsE 4 = Z_to_bv 64 TP_gq ->
  (forall m' regs', W C A m' md -> cs_kept regsE regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 86912) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 regsE s pixs ret S CK HW0 Hs16 Hlo Hhi H2 H3 H4 H10 HCSR SV1 SV8 SV9 HE1 Hret HE2 HE4 HC.
  unfold TP_gq in *.
  assert (HRA : ex_keep (Z_to_bv 64 (bv_unsigned (getr regsE ex_rg1)) = ret)) by (unfold ex_keep; rewrite zbv_self; exact HE1).
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  assert (HE2k : ex_keep (getr regsE ex_r2 = Z_to_bv 64 s)) by exact HE2.
  assert (HE4k : ex_keep (getr regsE ex_r4 = Z_to_bv 64 284096)) by exact HE4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); 0%Z; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
  }
  pose (STOPS := STOPS_fuzz_B0).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); 0%Z; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); 0%Z; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); 0%Z; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BSF := [(32%nat, s)]).
  exW_regfactB BSF HR ex_r10 G10.
  assert (CSF : cs_kept regsE RcF).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exT_cs_of_al EE sr regsE RcF [(2%nat, EVar 32); (3%nat, EVar 3); (4%nat, ELit 284096); (8%nat, EVar 36); (9%nat, EVar 37); (18%nat, EVar 18); (19%nat, EVar 19); (20%nat, EVar 20); (21%nat, EVar 21); (22%nat, EVar 22); (23%nat, EVar 23); (24%nat, EVar 24); (25%nat, EVar 25); (26%nat, EVar 26); (27%nat, EVar 27)] HR) end.
    { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). constructor; [symmetry; exact HE2k|]. constructor; [exact HG3|]. constructor; [symmetry; exact HE4k|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact K18|]. constructor; [exact K19|]. constructor; [exact K20|]. constructor; [exact K21|]. constructor; [exact K22|]. constructor; [exact K23|]. constructor; [exact K24|]. constructor; [exact K25|]. constructor; [exact K26|]. constructor; [exact K27|]. constructor. }
    { vm_compute; reflexivity. } }
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC M0 RcF HWs0 CSF G10).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_fuzz_B1 : list Z := [86924]%Z.
Lemma fuzz_B1 : forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 10 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  (1 <= pixs < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  getr regsE 1 = ret -> ret_ok ret -> getr regsE 2 = Z_to_bv 64 s -> getr regsE 4 = Z_to_bv 64 TP_gq ->
  (forall m' regs', W C A m' md -> POSTM C A s m m' ->
     getr regs' 2 = Z_to_bv 64 (s + -48) -> getr regs' 3 = getr regsE 3 -> getr regs' 4 = Z_to_bv 64 TP_gq -> getr regs' 8 = Z_to_bv 64 pixs -> gq_csrest regs' regsE ->
     rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
     realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 86924) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 86912) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 regsE s pixs ret S CK HW0 Hs16 Hlo Hhi H2 H3 H4 H10 HCSR RRpixs SV1 SV8 SV9 HE1 Hret HE2 HE4 HC.
  unfold TP_gq in *.
  assert (HRA : ex_keep (Z_to_bv 64 (bv_unsigned (getr regsE ex_rg1)) = ret)) by (unfold ex_keep; rewrite zbv_self; exact HE1).
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  assert (HE2k : ex_keep (getr regsE ex_r2 = Z_to_bv 64 s)) by exact HE2.
  assert (HE4k : ex_keep (getr regsE ex_r4 = Z_to_bv 64 284096)) by exact HE4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
  }
  pose (STOPS := STOPS_fuzz_B1).
  assert (HKp0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 34) 1 (2 ^ 64 - 1)]).
  { ex_know r0. }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose proof (u64_range (getr regsE ex_rg1)) as RRs1. pose proof (u64_range (getr regsE ex_rg8)) as RRs8. pose proof (u64_range (getr regsE ex_rg9)) as RRs9.
  pose (BSF := [(32%nat, s); (34%nat, pixs); (35%nat, bv_unsigned (getr regsE ex_rg1)); (36%nat, bv_unsigned (getr regsE ex_rg8)); (37%nat, bv_unsigned (getr regsE ex_rg9))]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat C1. exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat C8. exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat C9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cp.
  exW_regfactW r0 HR ex_r18 G18. exW_regfactW r0 HR ex_r19 G19. exW_regfactW r0 HR ex_r20 G20. exW_regfactW r0 HR ex_r21 G21. exW_regfactW r0 HR ex_r22 G22. exW_regfactW r0 HR ex_r23 G23. exW_regfactW r0 HR ex_r24 G24. exW_regfactW r0 HR ex_r25 G25. exW_regfactW r0 HR ex_r26 G26. exW_regfactW r0 HR ex_r27 G27.
  assert (CSRF : gq_csrest RcF regsE).
  { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). unfold gq_csrest. exact (conj (eq_trans G18 K18) (conj (eq_trans G19 K19) (conj (eq_trans G20 K20) (conj (eq_trans G21 K21) (conj (eq_trans G22 K22) (conj (eq_trans G23 K23) (conj (eq_trans G24 K24) (conj (eq_trans G25 K25) (conj (eq_trans G26 K26) (eq_trans G27 K27)))))))))). }
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC M0 RcF HWs0 PMs0 G2 (eq_trans G3 HG3) G4 G8 CSRF C1 C8 C9 Cp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_tail : list Z := [94372]%Z.
Lemma fuzz_tail : forall (fx : FPState) C A m md regs (regsE : bvmap 5 word) (s pixs cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 TP_gq -> getr regs 8 = Z_to_bv 64 pixs -> gq_csrest regs regsE ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  getr regsE 1 = ret -> ret_ok ret -> getr regsE 2 = Z_to_bv 64 s -> getr regsE 4 = Z_to_bv 64 TP_gq ->
  PIXat m pixs v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 (p_data v)) = Some R -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> (0 < R)%Z -> p_data v <> pixs ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ p_data v <> cm /\ p_data v <> c_arr cv /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regsE regs' -> pixd_post A A' pixs (p_data v) cm (c_arr cv) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 87240) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 regsE s pixs cm karr R v cv ret S CK HW0 Hs16 HloF Hhi H2 H3 H4 H8 HCSR SV1 SV8 SV9 LCp HE1 Hret HE2 HE4 PXs Hrc Htx Hcm Lpixs_a0 F0pixs Ldata_a0 F0data HR0 NEdp HCM HC.
  unfold TP_gq, GQ_STACK_F in *.
  assert (Hlo : (c_top C - LSTK + 48 <= s)%Z) by lia.
  assert (HRA : ex_keep (Z_to_bv 64 (bv_unsigned (getr regsE ex_rg1)) = ret)) by (unfold ex_keep; rewrite zbv_self; exact HE1).
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  assert (HE2k : ex_keep (getr regsE ex_r2 = Z_to_bv 64 s)) by exact HE2.
  assert (HE4k : ex_keep (getr regsE ex_r4 = Z_to_bv 64 284096)) by exact HE4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 48)%Z) by lia.
  assert (GLO2 : (s - 48 + Z.of_nat (Z.to_nat 48) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (48 <= s)%Z) by lia.
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430128 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37); KWord (SA (EVar 32) (-32)) 8 (EVar 34)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCp].
  }
  pose (STOPS := STOPS_tail).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 48) (Z.to_nat 48) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 48 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 48 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 48 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  pose (BSx0 := [(32%nat, s); (34%nat, pixs)]).
  exW_cellB HK Hlf r0 BSx0 (EVar 32) s (-32)%Z 8%nat CELLpp.
  clear BSx0.
  assert (PXsM0 : PIXat M0 pixs v) by exact (exT_pix_sess C A0 m0 M0 _ s 48 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (HCM0 : cm = 0%Z \/ (CMAPat M0 cm cv /\ live A0 (Z_to_bv 64 cm) = Some 24%Z /\ live A0 (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ p_data v <> cm /\ p_data v <> c_arr cv /\ (0 < karr)%Z)).
  { destruct HCM as [Z0 | (CM & Lc & REST)]; [left; exact Z0 | right]. split; [exact (exT_cmap_sess C A0 m0 M0 _ s 48 cm cv CK HW0 GLO1 Lc CM FRs0) | split; [exact Lc | exact REST]]. }
  assert (PPlo : (s + OFF0 <= s + -32)%Z) by (unfold OFF0; lia). assert (PPhi : (s + -32 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_keep_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) (s + -32) pixs cm karr R v cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, ALLOC_STACK; lia) PPlo PPhi Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_0 CELLpp
             PXsM0 Hrc Htx Hcm Lpixs_a0 F0pixs Ldata_a0 F0data HR0 NEdp HCM0) end end.
  intros A1 m1 vm1 r1 HW1 CSx0 PDP PMc0 CELL0 FRMs0 RTR0.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (FRMx0 : FRM C (s + -24) M0 m1).
  { replace (s + -24)%Z with (s + -32 + 8)%Z by lia. exact (proj1 PMc0). }
  pose proof (sub_live_refl A1) as SUB1. pose proof (POSTM_refl C A1 s m1) as PM1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, (-24)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-24) 48 M0 m1 E0 (EVar 32) CK FRMx0 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 CS0 OFF0 CELLpp PXsM0 HCM0 PPlo PPhi PMc0 FRMx0 CELL0 FRMs0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 48) (Z.to_nat 48) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 71) (EVar 32) (exW_canary SEGS 415784 m1) s 48 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A1 m1 _ E1 log1 (EVar 32) s 48 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  assert (CSF : cs_kept regsE RcF).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exT_cs_of_al EE sr regsE RcF [(2%nat, EVar 32); (3%nat, EVar 3); (4%nat, ELit 284096); (8%nat, EVar 36); (9%nat, EVar 37); (18%nat, EVar 18); (19%nat, EVar 19); (20%nat, EVar 20); (21%nat, EVar 21); (22%nat, EVar 22); (23%nat, EVar 23); (24%nat, EVar 24); (25%nat, EVar 25); (26%nat, EVar 26); (27%nat, EVar 27)] HR) end.
    { destruct HCSR as (K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27). constructor; [symmetry; exact HE2k|]. constructor; [exact HG3|]. constructor; [symmetry; exact HE4k|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact K18|]. constructor; [exact K19|]. constructor; [exact K20|]. constructor; [exact K21|]. constructor; [exact K22|]. constructor; [exact K23|]. constructor; [exact K24|]. constructor; [exact K25|]. constructor; [exact K26|]. constructor; [exact K27|]. constructor. }
    { vm_compute; reflexivity. } }
  exact (HC A1 M1 vm1 RcF HWs1 CSF PDP RTR0 G10).
Qed.
End Chain.
End V15LeptFuzz.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Drv1.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL11a.
Module V15LeptFuzzMain.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
Import V15Drv1.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import V15CL9a.
Import V15CL11a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL14a.
Import V15CL15a.
Import V15CL16a.
Import V15LeptFuzz.
(* [comment removed for export] *)









Import V15Drv1.V15FuzzIface.


Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.

Import V15CL9a.V15LeptPixDestroy.

Import V15CL11a.V15LeptDeser.


Import V15CL14a.V15LeptDither_iface.

Import V15CL15a.V15LeptOwn.

Import V15CL16a.V15LeptGq_iface.

Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Segs.
Variable rom : word -> option byte.

Definition FZ3 (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1))) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
         (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

(* [comment removed for export] *)
Lemma fz_small : forall (fx : FPState) regs m (s sz dp : Z) (ret : word),
  (48 <= s)%Z -> (s < 2 ^ 63)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 sz ->
  exists regs', msteps SEGS (@mkst fx regs (Z_to_bv 64 86856) m rom) (@mkst fx regs' ret (FZ3 m s regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof.
  intros fx regs m s sz dp ret Hs Hs63 Hsz Hret SOK H2 H1 H10 H11.
  ex_entry regs [s; dp; sz] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; dp; sz]) m [KRange (EVar 32) 48 (2 ^ 63); KRange (EVar 34) 0 2; KWr (SA (EVar 32) (-48)) 48]).
  { ex_know regs. }
  ex_run 200%nat [87268%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - lazymatch type of Hms with msteps ?sg _ (mkst _ (Z_to_bv 64 ?pc) _ _) =>
      let F := fresh "F" in let D := fresh "D" in ex_fetch sg pc F D;
      lazymatch type of D with decode_any ?w = Some (Jalr ?rd ?rs1 ?imm, _) =>
        pose proof (exT_ret_step fx sg R' pc _ rom w rd rs1 imm ret _ Hms F (eq_refl _) D ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl 0%Z))
                      ltac:(etransitivity; [exact (reg_val _ _ _ rs1 HR') | exact H1]) Hret) as Hms' end end.
    unfold FZ3. ex_mem regs Hms'.
  - split; [ex_reg regs HR' | ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma fz_A : forall (fx : FPState) regs m (s sz dp : Z),
  (48 <= s)%Z -> (s < 2 ^ 63)%Z -> (3 <= sz < 2 ^ 63)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  store_ok SEGS m (Z_to_bv 64 217712) 8 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 sz ->
  exists regs', msteps SEGS (@mkst fx regs (Z_to_bv 64 86856) m rom)
                            (@mkst fx regs' (Z_to_bv 64 162088) (wbytes (FZ3 m s regs) (Z_to_bv 64 217712) (word_to_le_bytes 8 (Z_to_bv 64 87272))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 86912 /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 sz
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m s sz dp Hs Hs63 Hsz SOK SOKh H2 H10 H11.
  ex_entry regs [s; dp; sz] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; dp; sz]) m [KRange (EVar 32) 48 (2 ^ 63); KRange (EVar 34) 3 (2 ^ 63); KWr (SA (EVar 32) (-48)) 48; KWr (SA (ELit 0) 217712) 8]).
  { ex_know regs. }
  ex_run 200%nat [162088%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold FZ3; ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
Qed.
End Segs.

(* [comment removed for export] *)
Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_gq <= FUZZ_CALLS)%Z /\ (forall size, (0 <= size)%Z -> (RB_gq <= fuzz_margin size)%Z).
Proof. split; [unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS; lia | intros size _; unfold fuzz_margin, RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14; lia]. Qed.

Theorem lept_fuzz_call : F1_contract -> F2_contract -> F3_contract -> F4_contract -> F5_contract -> F6_contract -> @fuzz_call_contract AL CL ASR.
Proof.
  intros HF1 HF2 HF3 HF4 HF5 HF6. unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hz Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret H3 H4 Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm. pose proof (FZb size ltac:(lia)) as FZb'.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in H4.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  pose proof (u64_range (getr regs 2)) as Hs. pose proof (u64_range dptr) as Hdp. pose proof (u64_range sp0) as Hsp0r.
  set (s := u (getr regs 2)) in *.
  assert (H2 : getr regs 2 = Z_to_bv 64 s) by (subst s; rewrite zbv_self; reflexivity). clearbody s.
  set (dp := u dptr) in *.
  assert (Edp : dptr = Z_to_bv 64 dp) by (subst dp; rewrite zbv_self; reflexivity). clearbody dp. rewrite Edp in Ha0, Hlive, Hempty.
  set (C := LCTX sp0 argv envp s (m_vmmaps md) m A).
  assert (Etop : c_top C = s) by reflexivity. assert (Evm : c_vm C = m_vmmaps md) by reflexivity.
  assert (CK : Cok C) by (constructor; cbn; rewrite ?LSTK_val; lia).
  pose proof LSTK_val as LV.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT3 : forall a : word, ~ (s - 24 <= u a < s)%Z -> FZ3 m s regs a = m a).
  { intros a Ha. unfold FZ3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (GR3 : mem_grows m (FZ3 m s regs)) by (unfold FZ3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom fx regs m s size dp ret ltac:(lia) ltac:(lia) ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K fx A (FZ3 m s regs) (m_vmmaps md) r1 Hz).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 24)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - intros r Hr. apply AG1. intros Hin. cbn [In] in Hin. unfold callee_saved in Hr.
      destruct Hin as [<-|[<-|[]]]; repeat (destruct Hr as [X|Hr]; [apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X|]); destruct Hr as [Y1 _]; vm_compute in Y1; exfalso; apply Y1; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - apply (aroom_mono A (m_vmmaps md) kR bR); [exact Hrm | lia | lia]. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 217712) 8 = true) by exact Hhdl.
  destruct (fz_A al_rom fx regs m s size dp ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Ha0 Ha1) as (rE & RUNE & Q2e & Q1e & Q10e & Q11e & AGE).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUNE |].
  set (mE := wbytes (FZ3 m s regs) (Z_to_bv 64 217712) (word_to_le_bytes 8 (Z_to_bv 64 87272))) in *.
  assert (OUTE : forall a : word, ~ (s - 24 <= u a < s)%Z -> ~ (217712 <= u a < 217720)%Z -> mE a = m a).
  { intros a H1' H2'. subst mE. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GRE : mem_grows m mE) by (subst mE; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HWE : W C A mE md).
  { apply (W_entry C md mE CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LLU16] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 24)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 217712); [exfalso; apply NE; apply OUTE; lia|].
      all: destruct (Z_lt_ge_dec (u a) 217720); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUTE; lia].
    - exact GRE.
    - rewrite p16_segs. subst mE. cbn [ll_hcell ll_devnull LLU16]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A mE md (Z_to_bv 64 dp) size CK HWE Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KF : forall (fx' : FPState) A' mf vm' rr, frm_zero (@fp_csr fx') -> W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> aroom A' vm' (kR - RK_gq) (bR - RB_gq) -> realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros fx' A' mf vm' rr Hz' HWf LQ A0 CS HRf. apply (K fx' A' mf vm' rr Hz').
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
    - apply (aroom_mono A' vm' (kR - RK_gq) (bR - RB_gq)); [exact HRf | lia | lia]. }
  assert (Q4e : getr rE 4 = Z_to_bv 64 284096) by (rewrite (AGE 4) by notin_list; exact H4).
  replace (Z_to_bv 64 162088) with (162088 : word) by (apply bv_eq; reflexivity).
  apply (pixDeserialize_W (fx := fx) C A mE md rE (s - 48) dp pl (Z_to_bv 64 86912) S CK HWE Q2e ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1e ltac:(red; apply bv_eq; reflexivity) Q4e Q10e
           ltac:(rewrite Q11e, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia) ltac:(clear - Hal16; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q0 Eq0]; rewrite Eq0; replace (q0 * 16)%Z with (q0 * 4 * 4)%Z by lia; apply Z_mod_mult)
           kR bR Hrm ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
  unfold DK. intros A' m' vm' rD HW' CS' PM' RES Hrm'.
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (C1 : rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regs 1))).
  { change (s + -8)%Z with (s - 8)%Z. rewrite (FRM_rdn16 C (s - 48) mE m' (s - 8) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst mE. unfold FZ3. rdn_solve. }
  assert (C2 : rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { change (s + -16)%Z with (s - 16)%Z. rewrite (FRM_rdn16 C (s - 48) mE m' (s - 16) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst mE. unfold FZ3. rdn_solve. }
  assert (C3 : rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { change (s + -24)%Z with (s - 24)%Z. rewrite (FRM_rdn16 C (s - 48) mE m' (s - 24) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst mE. unfold FZ3. rdn_solve. }
  assert (Y2 : getr rD 2 = Z_to_bv 64 (s + -48)) by (rewrite (CS' 2) by (left; reflexivity); exact Q2e).
  assert (Y3 : getr rD 3 = getr regs 3) by (rewrite (CS' 3) by (right; left; reflexivity); apply AGE; notin_list).
  assert (Y4 : getr rD 4 = Z_to_bv 64 TP_gq) by (rewrite (CS' 4) by (right; right; left; reflexivity); exact Q4e).
  assert (YCS : gq_csrest rD regs).
  { unfold gq_csrest. repeat split; (etransitivity; [apply CS'; do 5 right; vm_compute; split; intros X; discriminate X | apply AGE; notin_list]). }
  assert (HloW : (c_top C - LSTK + 48 <= s)%Z) by (rewrite Etop, LV; lia).
  assert (HloF : (c_top C - LSTK + 48 + GQ_STACK_F <= s)%Z) by (rewrite Etop, LV; unfold GQ_STACK_F; lia).
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO & PF)].
  - (* [comment removed for export] *)
    apply (fuzz_B0 fx C A' m' _ rD regs s 0 ret S CK HW' Hsp16 HloW ltac:(rewrite Etop; lia) Y2 Y3 Y4 A0 YCS C1 C2 C3 Hra Hret H2 H4).
    intros mf rr HWf CSf A0f.
    apply (KF fx A' mf vm' rr Hz HWf LQ A0f CSf).
    apply (aroom_mono A' vm' (kR - RK_deser) (bR - RB_deser)); [exact Hrm' | clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia | clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & LpC0 & Ld & LdA & LdC0 & NEdp & RC & RQ).
    pose proof PF as (Ev & HOK & Hw & Hh & CMOK).
    destruct v as [w h d spp wpl rc xres yres fmt spec text cm datas].
    cbn in PX, Rrc, Rtx, Hn4, Ld, LdA, LdC0, NEdp, RC, RQ, Ev, HOK, Hw, Hh, CMOK.
    injection Ev as E8 E7 E6 E5 E4 E3 E2 E1. subst spp wpl rc xres yres fmt spec text.
    change (PIXV w h d (spp_of d) (wpl_of w d) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z cm datas) with (hdv w h d cm datas) in PX.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
    assert (CMFd : cm_facts A' m' cm cv).
    { destruct RC as [Z0 | (Hc1 & CM & Lc & La & _)]; [left; exact Z0 | right]. split; [exact CM | split; [apply CMOK; lia | split; [exact Lc | exact La]]]. }
    apply (fuzz_B1 fx C A' m' _ rD regs s pix ret S CK HW' Hsp16 HloW ltac:(rewrite Etop; lia) Y2 Y3 Y4 A2p YCS ltac:(lia) C1 C2 C3 Hra Hret H2 H4).
    intros m0 r0 HW0 PM0 G2_0 G3_0 G4_0 G8_0 CSR0 C1_0 C8_0 C9_0 Cp_0.
    rename fx into fx0, A' into A0, vm' into vm0, Hz into FZ0, Hrm' into RM0.
    pose proof (exT_pix_livk A0 m' m0 pix _ PX (proj2 PM0) Lp) as PX0.
    pose proof (cmf_livk _ A0 A0 m' m0 cm cv CMFd (sub_live_refl A0) (proj2 PM0)) as CMF0.
    pose proof Lp as Lp0. pose proof Ld as Ld0.
    pose proof (fun q0 : word => eq_refl (live A0 q0)) as LQA0.
    (* [comment removed for export] *)
    apply (round_1 HF1 fx0 C A0 m0 _ r0 regs s pix w h d cm datas cv S FZ0 CK HW0 Hsp16 HloF (Z.le_refl _) G2_0 G3_0 G4_0 G8_0 CSR0 C1_0 C8_0 C9_0 Cp_0
             PX0 HOK Hw Hh Lp0 Ld0 CMF0 (kR - RK_deser)%Z (bR - RB_deser)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM0) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx1 A1 m1 vm1 r1 FZ1 HW1 PM1 LQ1 G2_1 G3_1 G4_1 G8_1 CSR1 C1_1 C8_1 C9_1 Cp_1 RM1.
    rewrite ?with_vmmaps_twice in HW1 |- *.
    assert (SUB1 : sub_live A0 A1) by (intros q0 k0 L0; rewrite LQ1; exact L0).
    pose proof (exT_pix_livk A0 m0 m1 pix _ PX0 (proj2 PM1) Lp0) as PX1.
    pose proof (cmf_livk _ A0 A1 m0 m1 cm cv CMF0 SUB1 (proj2 PM1)) as CMF1.
    pose proof (eq_trans (LQ1 _) Lp0) as Lp1. pose proof (eq_trans (LQ1 _) Ld0) as Ld1.
    pose proof (fun q0 : word => eq_trans (LQ1 q0) (LQA0 q0)) as LQA1.
    (* [comment removed for export] *)
    apply (round_2 HF2 fx1 C A1 m1 _ r1 regs s pix w h d cm datas cv S FZ1 CK HW1 Hsp16 HloF (Z.le_refl _) G2_1 G3_1 G4_1 G8_1 CSR1 C1_1 C8_1 C9_1 Cp_1
             PX1 HOK Hw Hh Lp1 Ld1 CMF1 (kR - RK_deser - RK_pixcopy - RK_d2bpp)%Z (bR - RB_deser - RB_pixcopy14 - RB_d2bpp)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM1) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx2 A2 m2 vm2 r2 FZ2 HW2 PM2 LQ2 G2_2 G3_2 G4_2 G8_2 CSR2 C1_2 C8_2 C9_2 Cp_2 RM2.
    rewrite ?with_vmmaps_twice in HW2 |- *.
    assert (SUB2 : sub_live A1 A2) by (intros q0 k0 L0; rewrite LQ2; exact L0).
    pose proof (exT_pix_livk A1 m1 m2 pix _ PX1 (proj2 PM2) Lp1) as PX2.
    pose proof (cmf_livk _ A1 A2 m1 m2 cm cv CMF1 SUB2 (proj2 PM2)) as CMF2.
    pose proof (eq_trans (LQ2 _) Lp1) as Lp2. pose proof (eq_trans (LQ2 _) Ld1) as Ld2.
    pose proof (fun q0 : word => eq_trans (LQ2 q0) (LQA1 q0)) as LQA2.
    (* [comment removed for export] *)
    apply (round_3 HF3 fx2 C A2 m2 _ r2 regs s pix w h d cm datas cv S FZ2 CK HW2 Hsp16 HloF (Z.le_refl _) G2_2 G3_2 G4_2 G8_2 CSR2 C1_2 C8_2 C9_2 Cp_2
             PX2 HOK Hw Hh Lp2 Ld2 CMF2 (kR - RK_deser - RK_pixcopy - RK_d2bpp - RK_pixcopy - RK_dbin)%Z (bR - RB_deser - RB_pixcopy14 - RB_d2bpp - RB_pixcopy14 - RB_dbin)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM2) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx3 A3 m3 vm3 r3 FZ3 HW3 PM3 LQ3 G2_3 G3_3 G4_3 G8_3 CSR3 C1_3 C8_3 C9_3 Cp_3 RM3.
    rewrite ?with_vmmaps_twice in HW3 |- *.
    assert (SUB3 : sub_live A2 A3) by (intros q0 k0 L0; rewrite LQ3; exact L0).
    pose proof (exT_pix_livk A2 m2 m3 pix _ PX2 (proj2 PM3) Lp2) as PX3.
    pose proof (cmf_livk _ A2 A3 m2 m3 cm cv CMF2 SUB3 (proj2 PM3)) as CMF3.
    pose proof (eq_trans (LQ3 _) Lp2) as Lp3. pose proof (eq_trans (LQ3 _) Ld2) as Ld3.
    pose proof (fun q0 : word => eq_trans (LQ3 q0) (LQA2 q0)) as LQA3.
    (* [comment removed for export] *)
    apply (round_4 HF4 fx3 C A3 m3 _ r3 regs s pix w h d cm datas cv S FZ3 CK HW3 Hsp16 HloF (Z.le_refl _) G2_3 G3_3 G4_3 G8_3 CSR3 C1_3 C8_3 C9_3 Cp_3
             PX3 HOK Hw Hh Lp3 Ld3 CMF3 (kR - RK_deser - RK_pixcopy - RK_d2bpp - RK_pixcopy - RK_dbin - RK_pixcopy - RK_mask)%Z (bR - RB_deser - RB_pixcopy14 - RB_d2bpp - RB_pixcopy14 - RB_dbin - RB_pixcopy14 - RB_mask)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM3) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx4 A4 m4 vm4 r4 FZ4 HW4 PM4 LQ4 G2_4 G3_4 G4_4 G8_4 CSR4 C1_4 C8_4 C9_4 Cp_4 RM4.
    rewrite ?with_vmmaps_twice in HW4 |- *.
    assert (SUB4 : sub_live A3 A4) by (intros q0 k0 L0; rewrite LQ4; exact L0).
    pose proof (exT_pix_livk A3 m3 m4 pix _ PX3 (proj2 PM4) Lp3) as PX4.
    pose proof (cmf_livk _ A3 A4 m3 m4 cm cv CMF3 SUB4 (proj2 PM4)) as CMF4.
    pose proof (eq_trans (LQ4 _) Lp3) as Lp4. pose proof (eq_trans (LQ4 _) Ld3) as Ld4.
    pose proof (fun q0 : word => eq_trans (LQ4 q0) (LQA3 q0)) as LQA4.
    (* [comment removed for export] *)
    apply (round_5 HF5 fx4 C A4 m4 _ r4 regs s pix w h d cm datas cv S FZ4 CK HW4 Hsp16 HloF (Z.le_refl _) G2_4 G3_4 G4_4 G8_4 CSR4 C1_4 C8_4 C9_4 Cp_4
             PX4 HOK Hw Hh Lp4 Ld4 CMF4 (kR - RK_deser - RK_pixcopy - RK_d2bpp - RK_pixcopy - RK_dbin - RK_pixcopy - RK_mask - RK_pixcopy - RK_mask)%Z (bR - RB_deser - RB_pixcopy14 - RB_d2bpp - RB_pixcopy14 - RB_dbin - RB_pixcopy14 - RB_mask - RB_pixcopy14 - RB_mask)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM4) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx5 A5 m5 vm5 r5 FZ5 HW5 PM5 LQ5 G2_5 G3_5 G4_5 G8_5 CSR5 C1_5 C8_5 C9_5 Cp_5 RM5.
    rewrite ?with_vmmaps_twice in HW5 |- *.
    assert (SUB5 : sub_live A4 A5) by (intros q0 k0 L0; rewrite LQ5; exact L0).
    pose proof (exT_pix_livk A4 m4 m5 pix _ PX4 (proj2 PM5) Lp4) as PX5.
    pose proof (cmf_livk _ A4 A5 m4 m5 cm cv CMF4 SUB5 (proj2 PM5)) as CMF5.
    pose proof (eq_trans (LQ5 _) Lp4) as Lp5. pose proof (eq_trans (LQ5 _) Ld4) as Ld5.
    pose proof (fun q0 : word => eq_trans (LQ5 q0) (LQA4 q0)) as LQA5.
    (* [comment removed for export] *)
    apply (round_6 HF6 fx5 C A5 m5 _ r5 regs s pix w h d cm datas cv S FZ5 CK HW5 Hsp16 HloF (Z.le_refl _) G2_5 G3_5 G4_5 G8_5 CSR5 C1_5 C8_5 C9_5 Cp_5
             PX5 HOK Hw Hh Lp5 Ld5 CMF5 (kR - RK_deser - RK_pixcopy - RK_d2bpp - RK_pixcopy - RK_dbin - RK_pixcopy - RK_mask - RK_pixcopy - RK_mask - RK_pixcopy - RK_mask)%Z (bR - RB_deser - RB_pixcopy14 - RB_d2bpp - RB_pixcopy14 - RB_dbin - RB_pixcopy14 - RB_mask - RB_pixcopy14 - RB_mask - RB_pixcopy14 - RB_mask)%Z ltac:(rewrite ?with_vmmaps_vmmaps; exact RM5) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)).
    intros fx6 A6 m6 vm6 r6 FZ6 HW6 PM6 LQ6 G2_6 G3_6 G4_6 G8_6 CSR6 C1_6 C8_6 C9_6 Cp_6 RM6.
    rewrite ?with_vmmaps_twice in HW6 |- *.
    assert (SUB6 : sub_live A5 A6) by (intros q0 k0 L0; rewrite LQ6; exact L0).
    pose proof (exT_pix_livk A5 m5 m6 pix _ PX5 (proj2 PM6) Lp5) as PX6.
    pose proof (cmf_livk _ A5 A6 m5 m6 cm cv CMF5 SUB6 (proj2 PM6)) as CMF6.
    pose proof (eq_trans (LQ6 _) Lp5) as Lp6. pose proof (eq_trans (LQ6 _) Ld5) as Ld6.
    pose proof (fun q0 : word => eq_trans (LQ6 q0) (LQA5 q0)) as LQA6.
    (* [comment removed for export] *)
    assert (HCM6 : cm = 0%Z \/ (CMAPat m6 cm cv /\ live A6 (Z_to_bv 64 cm) = Some 24%Z /\ live A6 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ datas <> cm /\ datas <> c_arr cv /\ (0 < 4 * c_nalloc cv)%Z)).
    { destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & LcC0 & LaC0 & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      destruct CMF6 as [Z0 | (CM6 & _)]; [exfalso; lia|].
      split; [exact CM6|]. split; [rewrite LQA6; exact Lc|]. split; [rewrite LQA6; exact La|]. repeat (split; [assumption|]). exact Hna. }
    apply (fuzz_tail fx6 C A6 m6 _ r6 regs s pix cm (4 * c_nalloc cv)%Z (4 * (wpl_of w d * h))%Z (hdv w h d cm datas) cv ret S CK HW6 Hsp16 HloF (Z.le_refl _)
             G2_6 G3_6 G4_6 G8_6 CSR6 C1_6 C8_6 C9_6 Cp_6 Hra Hret H2 H4 PX6 eq_refl eq_refl eq_refl Lp6 LpC0 Ld6 LdC0 Hn4 NEdp HCM6).
    intros A7 mf vm7 rr HWf CSf PDP RTR A0f.
    rewrite ?with_vmmaps_twice in HWf |- *.
    apply (KF fx6 A7 mf vm7 rr FZ6 HWf).
    + destruct PDP as (D1 & D2 & D3 & D4). cbn in D2, D3, D4.
      assert (NZd : datas <> 0%Z).
      { destruct (blk_range C A0 m' _ (Z_to_bv 64 datas) _ CK HW' Ld Hn4) as [Gd _]. pose proof (wf_data _ WF) as Rd. cbn in Rd. rewrite u_Z2bv in Gd by lia. lia. }
      intros q0. destruct (bv_eq_dec _ q0 (Z_to_bv 64 pix)) as [->|N1]; [rewrite D1; symmetry; exact LpA|].
      destruct (bv_eq_dec _ q0 (Z_to_bv 64 datas)) as [->|N2]; [rewrite (D2 NZd); symmetry; exact LdA|].
      destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & _)].
      * rewrite (D4 q0 N1 (fun _ => N2) (fun X => False_ind _ (X Z0))), (LQA6 q0). apply RQ; [exact N1 | exact N2 | intros X; contradiction].
      * assert (NZc : cm <> 0%Z) by lia.
        destruct (bv_eq_dec _ q0 (Z_to_bv 64 cm)) as [->|N3]; [rewrite (proj1 (D3 NZc)); symmetry; exact LcA|].
        destruct (bv_eq_dec _ q0 (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite (proj2 (D3 NZc)); symmetry; exact LaA|].
        rewrite (D4 q0 N1 (fun _ => N2) (fun _ => conj N3 N4)), (LQA6 q0). apply RQ; [exact N1 | exact N2 | intros _; split; assumption].
    + exact A0f.
    + exact CSf.
    + pose proof (RTR _ _ ltac:(rewrite ?with_vmmaps_vmmaps; exact RM6) ltac:(clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia) ltac:(clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia)) as RM7.
      rewrite !Z.sub_0_r in RM7.
      apply (aroom_mono A7 vm7 _ _ _ _ RM7); [clear - Hrk FZk; unfold RK_gq, RK_deser, RK_pixcopy, RK_cmapcopy, RK_d2bpp, RK_dbin, RK_mask, RK_thr_gq, RK_rmc, RK_cml, RK_pix, FUZZ_CALLS in *; lia | clear - Hrb FZb'; unfold RB_gq, RB_deser, RB_pixcopy14, RB_cmapcopy, RB_d2bpp, RB_dbin, RB_mask, RB_thr_gq, RB_rmc, RB_cml, RB_pix14 in *; lia].
Qed.
End Final.
End V15LeptFuzzMain.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Kit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL17a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptRmc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptMaskBand.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBandLoopW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptMask32.
Module V15LeptPinsI.
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
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import V15Kit.
Import V15Drv1.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
(* [comment removed for export] *)







Import V15Kit.V15MallocLayout.

Import V15Drv1.V15FuzzIface.









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
    + rewrite (rdn_agree_on _ M M' 0x6584b 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x65878 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
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

#[export] Instance u16_pins16 : @V15Pins (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem u16_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16), @fuzz_call_contract (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16) ASR.
Proof.
  intros ASR.
  pose proof (@V15LeptRmc.pixRemoveColormap_gray8_W _ _ ASR u16_lept_pins u16_pins16) as RMC. pose proof (@V15CL15a.V15LeptPixDestroyRc2.pixDestroy_rc2_W _ _ ASR u16_lept_pins u16_pins16) as RC2.
  apply (@V15LeptFuzzMain.lept_fuzz_call _ _ ASR u16_lept_pins u16_pins16).
  - exact (@V15CL17a.V15LeptGqWrap.F1_W _ _ ASR u16_lept_pins u16_pins16 (@V15CL17a.V15LeptDithTop.pixDitherTo2bpp_Wc _ _ ASR u16_lept_pins u16_pins16) (@V15CL15a.V15LeptDithErr.pixDitherTo2bpp_d_W _ _ ASR u16_lept_pins u16_pins16)).
  - exact (@V15CL17a.V15LeptGqWrap.F2_W _ _ ASR u16_lept_pins u16_pins16 (@V15CL17a.V15LeptDithTop.pixDitherToBinary_Wc _ _ ASR u16_lept_pins u16_pins16) (@V15CL15a.V15LeptDithErr.pixDitherToBinary_d_W _ _ ASR u16_lept_pins u16_pins16)).
  - exact (@V15LeptMaskBand.F3_W _ _ ASR u16_lept_pins u16_pins16 RC2 (@V15LeptBandLoopW.band_loop_hop_W _ _ ASR u16_lept_pins u16_pins16)).
  - exact (@V15LeptMask32.F4_W _ _ ASR u16_lept_pins u16_pins16).
  - exact (@V15LeptMask32.F5_W _ _ ASR u16_lept_pins u16_pins16).
  - exact (@V15CL17a.V15LeptGqWrap.F6_W _ _ ASR u16_lept_pins u16_pins16 RMC RC2).
Qed.
End V15LeptPinsI.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefLayout.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15Main.
Module V15Pins.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import V15Kit.
Import V15Drv1.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V15Kit.V15MallocLayout. Import V15Kit.V15Startup. Import V15Kit.V15StartupDefs. Import V15Kit.V15StartupFacts.

Import V15Drv1.V15MainEntry. Import V15Drv1.V15Open. Import V15Drv1.V15Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x6584b) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem u16_pins : @V15Main.pins (@mallocng_alloc_layout LU16).
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
    assert (LIBC : forall (a : Z) n, (0x454f0 <= a)%Z -> (a + Z.of_nat n <= 0x658b8)%Z -> (a + Z.of_nat n <= 0x4551c \/ 0x45520 <= a)%Z ->
              (a + Z.of_nat n <= 0x65600 \/ 0x65820 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x6584b) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x6584b%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x6584b%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x6584b) + Z.of_nat 0)%Z with 0x6584b%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x65878%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LU16]. change (bv_unsigned (Z_to_bv 64 0x65848) + 8)%Z with 0x65850%Z.
        rewrite (LIBC 0x65850%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x34228)) with 0x34228%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End V15Pins.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Spec.
Module V15Closed.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Spec.
Import V15Kit.
Import V15Pins.
Import V15Drv1.
Import V15LeptPinsI.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15Main.
(* [comment removed for export] *)







Import V15Kit.V15MallocLayout. Import V15Kit.V15Alloc. Import V15Kit.V15Sure.


Import V15Drv1.V15FuzzIface.

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
  exact (@V15Main.ref_realizes_spec_pins _ _ u16_sure V15Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
End V15Closed.
