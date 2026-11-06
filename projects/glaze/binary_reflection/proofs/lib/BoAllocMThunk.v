(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_e1c80_e1c88.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_e1c80 : bv 32 := @BV 32 0x8dc8d06f%Z I.
Lemma F_e1c80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xe1c80%Z I : word) = Some W_e1c80.
Proof. vm_refl. Qed.
Lemma D_e1c80 : decode_any W_e1c80 = Some (Jal (@BV 5 0%Z I) (@BV 21 1626332%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e1c84 : bv 32 := @BV 32 0xffdff06f%Z I.
Lemma F_e1c84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0xe1c84%Z I : word) = Some W_e1c84.
Proof. vm_refl. Qed.
Lemma D_e1c84 : decode_any W_e1c84 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097148%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_e1c80_e1c88.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFThunk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 Bo_code_e1c80_e1c88.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma jstep_lit : forall (fx : FPState) R M (p t : Z) w (imm : bv 21),
  fetch_word BSEGS (Z_to_bv 64 p) = Some w -> is_ecall w = false -> decode_any w = Some (Jal 0 imm, 4%Z) ->
  0 <= p < 2 ^ 64 -> t = p + bv_signed imm -> 0 <= t < 2 ^ 64 ->
  RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 p) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 t) M (seg_rom BSEGS)).
Proof.
  intros fx R M p t w imm Hf He Hd Hp Ht Htr.
  rewrite (step_jal_x0 BSEGS R (Z_to_bv 64 p) M (seg_rom BSEGS) w imm Hf He Hd).
  f_equal. f_equal. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold btgt, v_addi in G in change_no_check G' end). subst t. rewrite (u_Z2bv p) by lia. reflexivity.
Qed.

Lemma jstep_free_thunk : forall (fx : FPState) R M,
  RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 0x6ed5c) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS)).
Proof.
  intros. eapply (jstep_lit fx R M 0x6ed5c 0x6ed6c W_6ed5c);
    [ replace (Z_to_bv 64 0x6ed5c) with (0x6ed5c%bv : word) by (apply bv_eq; reflexivity); exact F_6ed5c
    | vm_compute; reflexivity | exact D_6ed5c | lia | vm_compute; reflexivity | lia ].
Qed.
Lemma jstep_opdel : forall (fx : FPState) R M,
  RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 0xe1c80) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 0x6ed5c) M (seg_rom BSEGS)).
Proof.
  intros. eapply (jstep_lit fx R M 0xe1c80 0x6ed5c W_e1c80);
    [ replace (Z_to_bv 64 0xe1c80) with (0xe1c80%bv : word) by (apply bv_eq; reflexivity); exact F_e1c80
    | vm_compute; reflexivity | exact D_e1c80 | lia | vm_compute; reflexivity | lia ].
Qed.
Lemma jstep_opdel_sz : forall (fx : FPState) R M,
  RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 0xe1c84) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 0xe1c80) M (seg_rom BSEGS)).
Proof.
  intros. eapply (jstep_lit fx R M 0xe1c84 0xe1c80 W_e1c84);
    [ replace (Z_to_bv 64 0xe1c84) with (0xe1c84%bv : word) by (apply bv_eq; reflexivity); exact F_e1c84
    | vm_compute; reflexivity | exact D_e1c84 | lia | vm_compute; reflexivity | lia ].
Qed.

Section THUNK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  (* [comment removed for export] *)
  Variable P : option Z -> ast -> Prop.
  #[local] Notation FKAT := (FREE_KAT BSEGS FXOK both_addrs (fun h => AAINVP (P h) bt)) (only parsing).

  (* [comment removed for export] *)
  Lemma free_kat_jstep_P : forall stk (e e' : Z),
    (forall (fx : FPState) R M, RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 e') M (seg_rom BSEGS))) ->
    FKAT stk e' -> FKAT stk e.
  Proof using BT_ia.
    intros stk e e' STEP FK. (lazymatch goal with |- ?G => let G' := eval unfold FREE_KAT in G in change_no_check G' end). intros h fx R M mdl Lc Lc' FF B C K B' C' K' ret sp p PRE.
    destruct PRE as (HH & HFX & AI & CP & HR10 & FPC & CASES).
    destruct AI as (st & W & RP & (BD & HLE) & MW).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end).
    apply (katD_step_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) (@mkst fx R (Z_to_bv 64 e') (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - reflexivity.
    - exact (STEP fx R (mrestrict (HID st mdl) M)).
    - intros mdl1 MI1 SBM1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS))) with M by reflexivity.
      rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      assert (PRE1 : free_pre BSEGS FXOK both_addrs (fun h => AAINVP (P h) bt) h stk fx R M mdl1 Lc Lc' FF B C K B' C' K' ret sp p).
      { split; [rewrite Ehl; exact HH|]. split; [exact HFX|]. split; [| split; [exact CP | split; [exact HR10 | split; [exact FPC | exact CASES]]]].
        exists st. split; [exact W|]. split; [exact (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1)|].
        split; [split; [exact BD | exact HLE] | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]. }
      apply (katD_conseq BSEGS _ _ _ (FK h fx R M mdl1 Lc Lc' FF B C K B' C' K' ret sp p PRE1)).
      intros c' (fx' & R' & M' & mdl' & Ec & HFX' & RK & CH & EK & SCR & AI' & SEV & LZK & HH').
      exists fx', R', M', mdl'. split; [exact Ec|]. split; [exact HFX'|]. split; [exact RK|]. split; [exact CH|]. split; [exact EK|]. split; [exact SCR|].
      split; [exact AI'|]. split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
      split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity].
  Qed.

  Theorem free_kat_thunk_P : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_free_thunk both_addrs).
  Proof using BT_ia. intros stk FK. apply (free_kat_jstep_P stk _ (ia_free both_addrs)); [exact jstep_free_thunk | exact FK]. Qed.
  Theorem free_kat_opdel_P : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_opdel both_addrs).
  Proof using BT_ia. intros stk FK. apply (free_kat_jstep_P stk _ (ia_free_thunk both_addrs)); [exact jstep_opdel | exact (free_kat_thunk_P stk FK)]. Qed.
  Theorem free_kat_opdel_sz_P : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_opdel_sz both_addrs).
  Proof using BT_ia. intros stk FK. apply (free_kat_jstep_P stk _ (ia_opdel both_addrs)); [exact jstep_opdel_sz | exact (free_kat_opdel_P stk FK)]. Qed.
End THUNK.

(* [comment removed for export] *)
Section THUNK_H.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  #[local] Notation FKAT := (FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt)) (only parsing).
  Theorem free_kat_thunk : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_free_thunk both_addrs).
  Proof using BT_ia. intros stk FK. exact (free_kat_thunk_P bt FXOK BT_ia holes_le stk FK). Qed.
  Theorem free_kat_opdel : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_opdel both_addrs).
  Proof using BT_ia. intros stk FK. exact (free_kat_opdel_P bt FXOK BT_ia holes_le stk FK). Qed.
  Theorem free_kat_opdel_sz : forall stk, FKAT stk (ia_free both_addrs) -> FKAT stk (ia_opdel_sz both_addrs).
  Proof using BT_ia. intros stk FK. exact (free_kat_opdel_sz_P bt FXOK BT_ia holes_le stk FK). Qed.
End THUNK_H.
End BoAllocFThunk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 BoAllocFThunk.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Lemma jstep_malloc_thunk : forall (fx : FPState) R M,
  RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 0x6ed60) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 0x6ef3c) M (seg_rom BSEGS)).
Proof.
  intros. eapply (jstep_lit fx R M 0x6ed60 0x6ef3c W_6ed60);
    [ replace (Z_to_bv 64 0x6ed60) with (0x6ed60%bv : word) by (apply bv_eq; reflexivity); exact F_6ed60
    | vm_compute; reflexivity | exact D_6ed60 | lia | vm_compute; reflexivity | lia ].
Qed.

Section THUNK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  #[local] Abbreviation AAINVH := (AAINV_HS bt).

  (* [comment removed for export] *)
  Lemma malloc_pre_sbm : forall h stk fq fx R M mdl mdl1 Lc FF B C K ret n sp (st : ast),
    malloc_pre BSEGS FXOK both_addrs AAINVH h stk fq fx R M mdl Lc FF B C K ret n sp ->
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> MInv (a_aa st) mdl1 -> same_but_materialized mdl mdl1 ->
    (bounds st Lc B C K /\ holes_lsopt h st) ->
    malloc_pre BSEGS FXOK both_addrs AAINVH h stk fq fx R M mdl1 Lc FF B C K ret n sp.
  Proof using.
    intros h stk fq fx R M mdl mdl1 Lc FF B C K ret n sp st PRE W RP MI1 SBM1 BH.
    destruct PRE as (HH & HFX & AI & REST).
    destruct AI as (st0 & W0 & RP0 & BH0 & MW).
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _).
    split; [rewrite Ehl; exact HH|]. split; [exact HFX|]. split; [| exact REST].
    exists st. split; [exact W|]. split; [exact (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1)|].
    split; [exact BH | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)].
  Qed.

  Lemma malloc_katw_jstep : forall stk fq (e e' : Z),
    (forall (fx : FPState) R M, RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 e') M (seg_rom BSEGS))) ->
    MALLOC_KATW BSEGS FXOK both_addrs AAINVH stk e' fq -> MALLOC_KATW BSEGS FXOK both_addrs AAINVH stk e fq.
  Proof using BT_ia.
    intros stk fq e e' STEP MK. (lazymatch goal with |- ?G => let G' := eval unfold MALLOC_KATW in G in change_no_check G' end). intros h fx R M mdl Lc FF B C K ret n sp PRE.
    pose proof PRE as (HH & HFX & AI & _).
    destruct AI as (st & W & RP & BH & MW).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end).
    apply (katwD_step_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) (@mkst fx R (Z_to_bv 64 e') (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - reflexivity.
    - exact (STEP fx R (mrestrict (HID st mdl) M)).
    - intros mdl1 MI1 SBM1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS))) with M by reflexivity.
      rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      pose proof (malloc_pre_sbm h stk fq fx R M mdl mdl1 Lc FF B C K ret n sp st PRE W RP MI1 SBM1 BH) as PRE1.
      apply (katwD_conseq BSEGS _ _ _ _ _ (MK h fx R M mdl1 Lc FF B C K ret n sp PRE1)).
      + intros c' (fx' & R' & M' & mdl' & p & Ec & HFX' & RK & E10 & P16 & PBLK & PSEC & PLC & PFF & PDEF & SH1 & SH2 & SH3 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl', p. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity].
      + intros c' (fx' & R' & M' & mdl' & Ec & HFX' & RK & E10 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl'. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity].
  Qed.

  Theorem malloc_katw_thunk : forall stk fq,
    MALLOC_KATW BSEGS FXOK both_addrs AAINVH stk (ia_malloc both_addrs) fq -> MALLOC_KATW BSEGS FXOK both_addrs AAINVH stk (ia_malloc_thunk both_addrs) fq.
  Proof using BT_ia. intros stk fq MK. apply (malloc_katw_jstep stk fq _ (ia_malloc both_addrs)); [exact jstep_malloc_thunk | exact MK]. Qed.

  (* [comment removed for export] *)
  Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Z -> Prop.
  Hypothesis FRESH_sbm : forall Lc FF B C K M mdl mdl1 n, FRESH Lc FF B C K M mdl n -> same_but_materialized mdl mdl1 -> FRESH Lc FF B C K M mdl1 n.

  Lemma malloc_alt_jstep : forall stk fq (e e' : Z),
    (forall (fx : FPState) R M, RiscvSemantics.step BSEGS (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) = MachineOk (@mkst fx R (Z_to_bv 64 e') M (seg_rom BSEGS))) ->
    MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH stk e' fq -> MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH stk e fq.
  Proof using FRESH_sbm BT_ia.
    intros stk fq e e' STEP MK. (lazymatch goal with |- ?G => let G' := eval unfold MALLOC_ALT in G in change_no_check G' end). intros h fx R M mdl Lc FF B C K ret n sp PRE FR.
    pose proof PRE as (HH & HFX & AI & _).
    destruct AI as (st & W & RP & BH & MW).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end).
    apply (katsD_step_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS)) (@mkst fx R (Z_to_bv 64 e') (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - reflexivity.
    - exact (STEP fx R (mrestrict (HID st mdl) M)).
    - intros mdl1 MI1 SBM1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx R (Z_to_bv 64 e) M (seg_rom BSEGS))) with M by reflexivity.
      rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      pose proof (malloc_pre_sbm h stk fq fx R M mdl mdl1 Lc FF B C K ret n sp st PRE W RP MI1 SBM1 BH) as PRE1.
      apply (katsD_conseq BSEGS _ _ _ _ _ (MK h fx R M mdl1 Lc FF B C K ret n sp PRE1 (FRESH_sbm _ _ _ _ _ _ _ _ _ FR SBM1))).
      + intros c' (fx' & R' & M' & mdl' & p & Ec & HFX' & RK & E10 & P16 & PBLK & PSEC & PLC & PFF & PDEF & SH1 & SH2 & SH3 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl', p. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity].
      + intros c' (fx' & R' & M' & mdl' & Ec & HFX' & RK & E10 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl'. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity].
  Qed.

  Theorem malloc_alt_thunk : forall stk fq,
    MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH stk (ia_malloc both_addrs) fq -> MALLOC_ALT BSEGS FXOK both_addrs AAINVH FRESH stk (ia_malloc_thunk both_addrs) fq.
  Proof using FRESH_sbm BT_ia. intros stk fq MK. apply (malloc_alt_jstep stk fq _ (ia_malloc both_addrs)); [exact jstep_malloc_thunk | exact MK]. Qed.
End THUNK.
