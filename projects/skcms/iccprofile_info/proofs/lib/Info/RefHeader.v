(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec LibWritev RefNodes RefExitBase RefStdioDefs RefExit LibStdioCall RefMemcpyLib RefReadBase Hoare LibMaskBits StreamSim RefWorld RefTargetPre RefReadDefs Frame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfCfg.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefHeader_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibStdioCall.

Unset Lia Cache.
Import ListNotations. Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition STOPSh : list Z :=
  [0x1dbe0; 0x1dfe4; 0x1e0dc; 0x1e120; 0x12f28; 0x18348; 0x16a60; 0x12d58; 0x18fe8]%Z.
Definition FUELh : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runh (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELh true STOPSh scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENVh (content : list byte) (vals : list word) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition ax (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x309e8; J 5; J 6; J 7;
   ELit 2; gmx 32; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 5; ELit 3; ELit 65536; ELit 0x208d9; ELit 0;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_Hstack : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x164e8);
   KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x12a88); KWord (SA (EVar 0) (-88)) 8 (spx 32);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].

(* [comment removed for export] *)
Definition area_x : expr := EAlu ALU_AND (ax 24) (ELit 18446744073709547520).

(* [comment removed for export] *)
Definition kn_Hheap : list kentry :=
  [KAlign (EVar 2) 4096; KRange (EVar 2) 0x2000 0x7fff7f7ff000;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x52000 0x7fffff7ef000;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 2) 0) 4096;
   KDisj (SA (EVar 2) 0) 4096 (SA (EVar 3) 0) 69632;
   (* [comment removed for export] *)
   KDisj (SA (ELit 0) 0x10000) 0x042000 (SA (EVar 2) 0) 4096;
   KWr (SA (EVar 2) 0) 4096;
   KWord (SA (EVar 2) 0) 8 (EVar 41);
   KWord (SA area_x 0) 8 (EVar 41); KRange area_x 0x2000 0x7fff7f7ff000;
   KDisj (SA (ELit 0) 0x10000) 0x042000 (SA area_x 0) 4096;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA area_x 0) 4096;
   KWord (SA (EVar 2) 24) 8 (ax 24); KWord (SA (EVar 2) 32) 8 (ax 24);
   KWord (SA (EVar 2) 40) 8 (EVar 3);
   KWord (SA (EVar 2) 48) 4 (ELit 0); KWord (SA (EVar 2) 52) 4 (ELit 0);
   KWord (SA (EVar 2) 56) 8 (ELit 0x11b20);
   KWord (SA (EVar 3) 0) 8 (ax 24);
   KWord (SA (EVar 3) 28) 1 (ELit 0); KWord (SA (EVar 3) 29) 1 (ELit 160); KWord (SA (EVar 3) 30) 2 (ELit 1);
   KWord (SA (EVar 3) 65568) 1 (ELit 0);
   KWord (SA (EVar 3) 69623) 1 (ELit 0); KWord (SA (EVar 3) 69624) 4 (ELit 0xfdc);
   KZero (SA (EVar 3) 69628) (ELit 4)].

(* [comment removed for export] *)
Definition kn_Himage : list kentry :=
  [KWr (SA (ELit 0) 0x20000) 0x32000;
   KImg 0x0 0x1000; KImg 0x10000 0x20890; KImg 0x20891 0x208d9; KImg 0x308d9 0x30918; KImg 0x509f0 0x50a10;
   KWord (SA (ELit 0) 0x30920) 8 (ELit 0x30920);
   KWord (SA (ELit 0) 0x30940) 4 (EVar 4); KWord (SA (ELit 0) 0x30944) 4 (EVar 8);
   KImg 0x3094c 0x30998; KImg 0x309a0 0x309b8; KImg 0x309c0 0x309d8; KImg 0x309e8 0x309f8;
   KImg 0x30a00 0x509f0; KImg 0x50a28 0x50c54; KWord (SA (ELit 0) 0x50c58) 8 (EVar 42);
   KImg 0x50c60 0x50c68; KImg 0x50c79 0x50c80; KImg 0x50c88 0x50c90; KImg 0x50ca0 0x50ca8;
   KWord (SA (ELit 0) 0x50ca8) 8 (ELit 4096);
   KImg 0x50cb0 0x50ce0;
   KImg 0x50ce8 0x50cf0;
   KWord (SA (ELit 0) 0x50cf0) 8 (EVar 41);
   KWord (SA (ELit 0) 0x50cf8) 4 (ELit 1); KWord (SA (ELit 0) 0x50cfc) 4 (ELit 1);
   KWord (SA (ELit 0) 0x50d00) 8 (ELit 0);
   KWord (SA (ELit 0) 0x50d08) 8 (ax 64); KWord (SA (ELit 0) 0x50d10) 8 (ELit 100);
   KWord (SA (ELit 0) 0x50d18) 8 (ELit 0);
   KWord (SA (ELit 0) 0x50d28) 8 (EVar 2); KWord (SA (ELit 0) 0x50d30) 8 (EVar 2);
   KWord (SA (ELit 0) 0x50d38) 8 (ax 4096);
   KImg 0x50d40 0x50ea0;
   KWord (SA (ELit 0) 0x50ea0) 8 (ax 24);
   KImg 0x50ea8 0x51020;
   KWord (SA (ELit 0) 0x51020) 8 (ELit 1);
   KImg 0x51028 0x51080;
   KWord (SA (ELit 0) 0x51080) 1 (ELit 1);
   KImg 0x51081 0x51088;
   KImg 0x51098 0x52000;
   KRange (EVar 4) 1 4194303].

Definition kn_H : list kentry := kn_Hstack ++ kn_Hheap ++ kn_Himage.
(* [comment removed for export] *)
Definition kn_short : list kentry := kn_H ++ [KRange (EVar 5) 0 5].
(* [comment removed for export] *)
Definition kn_long : list kentry :=
  kn_H ++ [KRange (EVar 5) 6 65535;
           KWord (SA (EVar 3) 32) 1 (EVar 6); KWord (SA (EVar 3) 33) 1 (EVar 7);
           KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition NXh : nat := 43.

(* [comment removed for export] *)
Definition hsA := Eval vm_compute in runh scr0 (SS 0x12b84 sr_H [] kn_short NXh).
Definition srSA : list expr := Eval vm_compute in s_regs (fst (fst hsA)).
Definition knSA : list kentry := Eval vm_compute in kn_after hsA kn_short.
(* [comment removed for export] *)
Definition scS : stdio_res := Eval vm_compute in
  match stdio_call NXh srSA knSA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition NXh2 : nat := 75.
Definition srSB0 : list expr := Eval vm_compute in sc_sr scS.
Definition knSB0 : list kentry := Eval vm_compute in sc_kn scS.
Definition hsB := Eval vm_compute in runh scr0 (SS (sc_ret scS) srSB0 [] knSB0 NXh2).
Definition srSB : list expr := Eval vm_compute in s_regs (fst (fst hsB)).
Definition knSB : list kentry := Eval vm_compute in kn_after hsB knSB0.
(* [comment removed for export] *)
Definition knSB2 : list kentry := Eval vm_compute in kn_unfill knSB (EVar 3) 0 69632.
Definition srSC0 : list expr := sr_upd srSB (ridx 10) (ELit 0).
Definition hsC := Eval vm_compute in runh scr0 (SS 0x18774 srSC0 [] knSB2 NXh2).
Definition srSC : list expr := Eval vm_compute in s_regs (fst (fst hsC)).
Definition knSC : list kentry := Eval vm_compute in kn_after hsC knSB2.

(* [comment removed for export] *)
Definition scr_taken : scripts := SCR [true] [] [].
Definition hoA := Eval vm_compute in runh scr_taken (SS 0x12b84 sr_H [] kn_long NXh).
Definition srOA : list expr := Eval vm_compute in s_regs (fst (fst hoA)).
Definition knOA : list kentry := Eval vm_compute in kn_after hoA kn_long.
Definition scO : stdio_res := Eval vm_compute in
  match stdio_call NXh srOA knOA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srOB0 : list expr := Eval vm_compute in sc_sr scO.
Definition knOB0 : list kentry := Eval vm_compute in sc_kn scO.
Definition hoB := Eval vm_compute in runh scr0 (SS (sc_ret scO) srOB0 [] knOB0 NXh2).
Definition srOB : list expr := Eval vm_compute in s_regs (fst (fst hoB)).
Definition knOB : list kentry := Eval vm_compute in kn_after hoB knOB0.
Definition knOB2 : list kentry := Eval vm_compute in kn_unfill knOB (EVar 3) 0 69632.
Definition srOC0 : list expr := sr_upd srOB (ridx 10) (ELit 0).
Definition hoC := Eval vm_compute in runh scr0 (SS 0x18774 srOC0 [] knOB2 NXh2).
Definition srOC : list expr := Eval vm_compute in s_regs (fst (fst hoC)).
Definition knOC : list kentry := Eval vm_compute in kn_after hoC knOB2.

(* [comment removed for export] *)
Definition scr_fall : scripts := SCR [false] [] [].
Definition hkA := Eval vm_compute in runh scr_fall (SS 0x12b84 sr_H [] kn_long NXh).
Definition srK : list expr := Eval vm_compute in s_regs (fst (fst hkA)).
(* [comment removed for export] *)
Definition cfglen_x : expr := Eval vm_compute in nth 11 srK (ELit 0).
(* [comment removed for export] *)
Definition cfglen_v : expr := EVar 47.
Definition srT : list expr := Eval vm_compute in map (esub cfglen_x cfglen_v) srK.
Definition knT : list kentry := kn_long.

(* [comment removed for export] *)
Lemma hdr_itinerary_ok :
  (s_pc (fst (fst hsA)), snd (fst hsA)) = (0x18fe8%Z, [])
  /\ stdio_call NXh srSA knSA = Some scS /\ (sc_ret scS, sc_f scS, sc_fd scS) = (0x18d54%Z, 0x206a0%Z, 2%Z)
  /\ (s_pc (fst (fst hsB)), snd (fst hsB)) = (0x18770%Z, [])
  /\ (s_pc (fst (fst hsC)), snd (fst hsC)) = (0x16a60%Z, [])
  /\ (s_pc (fst (fst hoA)), snd (fst hoA)) = (0x18fe8%Z, [SCBr true BC_LTU (EVar 5) (EAlu ALU_ADD cfglen_x (ELit 6))])
  /\ stdio_call NXh srOA knOA = Some scO /\ (sc_ret scO, sc_f scO, sc_fd scO) = (0x18d54%Z, 0x206a0%Z, 2%Z)
  /\ (s_pc (fst (fst hoB)), snd (fst hoB)) = (0x18770%Z, [])
  /\ (s_pc (fst (fst hoC)), snd (fst hoC)) = (0x16a60%Z, [])
  /\ s_pc (fst (fst hkA)) = 0x12d58%Z /\ s_log (fst (fst hkA)) = [] /\ s_next (fst (fst hkA)) = 47%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
End WithFP1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.micromega.Lia.

(* [comment removed for export] *)
Section WithFP2. Context {FP : PropExec.FPState}.
Definition cfgF (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         cfglen_x.

Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 6) (vals_ev vals 7).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma cfgF_tab :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (bv_unsigned (cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
     (zseq 256)) (zseq 256) = true.
(* [comment removed for export] *)
Proof. exact PerfCfg.cfgF0_tab. Qed.

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgF_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). rewrite forallb_forall in T.
  specialize (T b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  apply bv_eq. rewrite T. symmetry. apply u_small.
  pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)). lia.
Qed.
End WithFP2.


(* [comment removed for export] *)
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetPre.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Section WithFP3. Context {FP : PropExec.FPState}.
Lemma cfglen_val : forall content vals,
  vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content) -> vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content) ->
  edenot (ENVh content vals) cfglen_x = Z_to_bv 64 (hdr_cfglen content).
Proof.
  intros content vals P6 P7. unfold ENVh. rewrite cfglen_x_cfgF, P6, P7.
  pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
  change (bv_modulus 8) with 256%Z in B0, B1.
  unfold hdr_cfglen, hdr_cfg. apply cfgF_val; unfold hdr_b0, hdr_b1; lia.
Qed.

Lemma hdr_cfglen_range : forall content, (0 <= hdr_cfglen content < 32768)%Z.
Proof. intros. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition sx8F (v7 : word) : word := ext_val true 0 1 v7.
Lemma sx8F_tab :
  forallb (fun b1 => Z.eqb (bv_unsigned (sx8F (Z_to_bv 64 b1)))
                           (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sx8F_val : forall b1, (0 <= b1 < 256)%Z ->
  sx8F (Z_to_bv 64 b1) = Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z.
Proof.
  intros b1 H1. pose proof sx8F_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  apply bv_eq. rewrite T. symmetry. apply u_small. destruct (b1 <? 128)%Z eqn:Eb; [apply Z.ltb_lt in Eb|apply Z.ltb_ge in Eb]; lia.
Qed.

(* [comment removed for export] *)
Lemma mod_eq_shift : forall a b k m, (0 < m)%Z -> (a = b + k * m)%Z -> (a mod m = b mod m)%Z.
Proof. intros a b k m Hm ->. apply Z_mod_plus_full. Qed.
End WithFP3.

End RefHeader_defs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefWseg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfWalkBz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec LibWritev RefNodes RefExitBase RefStdioDefs RefExit LibStdioCall RefMemcpyLib RefReadBase Hoare LibMaskBits StreamSim
  RefWorld RefTargetPre RefReadDefs Frame.
Import RefHeader_defs.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefWseg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfWalkBz.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition hdr_img_ranges : list (Z * Z) := img_clear_ivs.

(* [comment removed for export] *)
Record header_pre (sp0 p1 gm tid sec cnr : word) (area : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := HDR_PRE {
  (* [comment removed for export] *)
  hp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  hp_gp : getr R 3 = Z_to_bv 64 0x10800;
  hp_tp : getr R 4 = Z_to_bv 64 0x309e8;
  hp_s0 : getr R 8 = Z_to_bv 64 2;
  hp_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);
  hp_s2 : getr R 18 = p1;
  hp_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  hp_s4 : getr R 20 = Z_to_bv 64 3;
  hp_s5 : getr R 21 = Z_to_bv 64 65536;
  hp_s6 : getr R 22 = Z_to_bv 64 0x208d9;
  hp_s7 : getr R 23 = Z_to_bv 64 0;
  (* [comment removed for export] *)
  hp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  hp_gm  : (0x52000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  hp_area : (0x2000 <= area)%Z /\ (area + 4096 <= 0x7fff7f800000)%Z /\ (area mod 4096 = 0)%Z;
  hp_area_img : (area + 4096 <= 0x10000 \/ 0x53000 <= area)%Z;   (* [comment removed for export] *)
  hp_disj : (area + 4096 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= area)%Z;
  hp_tid : (0 < bv_unsigned tid < 2 ^ 22)%Z;
  hp_L   : (Z.of_nat (length content) < 65536)%Z;
  (* [comment removed for export] *)
  hp_stack : stack_writable M sp0;
  hp_ra   : cell M (bv_unsigned sp0 - 56) 8 0x164e8;
  hp_f64  : cell M (bv_unsigned sp0 - 64) 8 (bv_unsigned sp0 + 8);
  hp_f72  : cell M (bv_unsigned sp0 - 72) 8 2;
  hp_f80  : cell M (bv_unsigned sp0 - 80) 8 0x12a88;
  hp_f88  : cell M (bv_unsigned sp0 - 88) 8 (bv_unsigned sp0 + 32);
  hp_f96  : cell M (bv_unsigned sp0 - 96) 8 0;
  hp_f104 : cell M (bv_unsigned sp0 - 104) 8 0;
  hp_f112 : cell M (bv_unsigned sp0 - 112) 8 0;
  hp_f120 : cell M (bv_unsigned sp0 - 120) 8 0;
  (* [comment removed for export] *)
  hp_group : group_writable M gm;
  hp_gmeta : cell M (bv_unsigned gm) 8 (area + 24);
  hp_pm4   : M (Z_to_bv 64 (bv_unsigned gm + 28)) = Some (Z_to_bv 8 0);
  hp_pm3   : M (Z_to_bv 64 (bv_unsigned gm + 29)) = Some (Z_to_bv 8 160);
  hp_pm2   : cell M (bv_unsigned gm + 30) 2 1;
  hp_gzr   : M (Z_to_bv 64 (bv_unsigned gm + 65568)) = Some (Z_to_bv 8 0);
  hp_ge5   : M (Z_to_bv 64 (bv_unsigned gm + 69623)) = Some (Z_to_bv 8 0);
  hp_ge4   : cell M (bv_unsigned gm + 69624) 4 0xfdc;
  hp_gend  : zero_bytes M (bv_unsigned gm + 69628) 4;
  hp_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  (* [comment removed for export] *)
  hp_marea : forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
               store_ok RSEGS M (Z_to_bv 64 (area + d)) m = true;
  hp_check : cell M area 8 (bv_unsigned sec);
  hp_gprev : cell M (area + 24) 8 (area + 24);
  hp_gnext : cell M (area + 32) 8 (area + 24);
  hp_gmem  : cell M (area + 40) 8 (bv_unsigned gm);
  hp_gavail : cell M (area + 48) 4 0;
  hp_gfreed : cell M (area + 52) 4 0;
  hp_gW    : cell M (area + 56) 8 0x11b20;
  (* [comment removed for export] *)
  hp_secret : cell M 0x50cf0 8 (bv_unsigned sec);
  hp_init   : cell M 0x50cf8 4 1;
  hp_ctr    : cell M 0x50cfc 4 1;
  hp_fmh    : cell M 0x50d00 8 0;
  hp_am     : cell M 0x50d08 8 (area + 64);
  hp_amc    : cell M 0x50d10 8 100;
  hp_amac   : cell M 0x50d18 8 0;
  hp_mah    : cell M 0x50d28 8 area;
  hp_mat    : cell M 0x50d30 8 area;
  hp_amas   : cell M 0x50d38 8 (area + 4096);
  hp_active : cell M 0x50ea0 8 (area + 24);
  hp_usage  : cell M 0x51020 8 1;
  hp_seq    : cell M 0x51080 1 1;
  hp_tidc   : cell M 0x30940 4 (bv_unsigned tid);
  hp_errno  : exists e, (0 <= e < 2 ^ 32)%Z /\ cell M 0x30944 4 e;
  hp_self   : cell M 0x30920 8 0x30920;
  hp_guard  : cell M 0x50c58 8 (bv_unsigned cnr);
  hp_pagesz : cell M 0x50ca8 8 4096;
  hp_img    : forall lo hi i, In (lo, hi) hdr_img_ranges -> (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma data_wseg : wseg_ok RSEGS (Z_to_bv 64 0x20000) 204800 = true.
Proof using . exact RefWseg.wseg_1. Qed.

Lemma data_store_ok : forall M d m, (0 <= d)%Z -> (d + Z.of_nat m <= 0x32000)%Z ->
  store_ok RSEGS M (Z_to_bv 64 (0x20000 + d)) m = true.
Proof using .
  intros M d m Hd Hm.
  eapply (store_ok_window RSEGS M (Z_to_bv 64 0x20000) _ 204800 m 0x20000 0x52000);
    [reflexivity | reflexivity | cbn; lia | apply data_wseg | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Header.
  Context {AMB : Amb}.
  Variables (sp0 p1 gm tid sec cnr : word) (area : Z) (content : list byte).
  Variables (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs).
  Variables (R0 : bvmap 5 word) (M0 : word -> option byte).
  Hypothesis HP : header_pre sp0 p1 gm tid sec cnr area content R0 M0.
  Hypothesis Hmap : map_has (vm_maps VM) gm (Z_to_bv 64 69632) = true.

  Let L : Z := Z.of_nat (length content).
  Definition modelh : Model := model_post VM stdin0 fs0 tid.
  #[local] Notation ENVv := (ENVh content) (only parsing).

  (* [comment removed for export] *)
  Definition valsh (e : Z) : list word :=
    [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content);
     Z_to_bv 64 e] ++ junk_vals R0 ++ [sec; cnr].

  (* [comment removed for export] *)
  Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
  Proof using L.
    intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
    unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
    rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_sym : exists e, (0 <= e < 2 ^ 32)%Z /\
    regs_ok (ENVh content (valsh e)) sr_H R0 /\ know_ok RSEGS (ENVh content (valsh e)) M0 kn_H.
  Proof using HP.
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hgm Har Hai Hdj Htid HL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hinit Hctr Hfmh Ham Hamc Hamac Hmah Hmat Hamas Hact Hus Hseq Htc (e & He & Herr')
                    Hself Hgd Hpgs Himg].
    exists e. split; [exact He|].
    set (vals := valsh e). set (E := ENVh content vals).
    assert (E0 : ev E 0 = sp0) by reflexivity.
    assert (E1 : ev E 1 = p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 area) by reflexivity.
    assert (E3 : ev E 3 = gm) by reflexivity.
    assert (E4 : ev E 4 = tid) by reflexivity.
    assert (E5 : ev E 5 = Z_to_bv 64 L) by reflexivity.
    assert (E8 : ev E 8 = Z_to_bv 64 e) by reflexivity.
    assert (E41 : ev E 41 = sec) by reflexivity.
    assert (E42 : ev E 42 = cnr) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (9 + i) = getr R0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, vals, valsh. cbn [ev]. unfold vals_ev.
      change (9 + i)%nat with (length [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content);
                                        Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 e] + i)%nat.
      rewrite app_nth2_plus. rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; lia).
      unfold junk_vals. rewrite (nth_map_seq (fun i => getr R0 (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - (* [comment removed for export] *)
      apply RefReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_H RefReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (9 + n))) with (ev E (9 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?k) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite Rsp; f_equal; lia end).
      all: try (lazymatch goal with |- _ = edenot _ (gmx ?k) =>
                  unfold gmx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E3;
                  assumption end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 5)) with (ev E 5); rewrite E5; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - (* [comment removed for export] *)
      pose proof (proj1 Hsp) as Hspr. pose proof (proj2 Hsp) as Hspa.
      destruct Hgm as (Hgm1 & Hgm2 & Hgmal). destruct Har as (Har1 & Har2 & Haral).
      pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp. pose proof (u64_range tid) as Utid.
      assert (AX : forall k, (0 <= k <= 4096)%Z -> edenot E (ax k) = Z_to_bv 64 (area + k)).
      { intros k Hk. unfold ax. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E2.
        rewrite u_small by lia. reflexivity. }
      assert (SPX : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k)).
      { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E0. reflexivity. }
      assert (AREA : edenot E area_x = Z_to_bv 64 area).
      { unfold area_x. cbn [edenot]. rewrite AX by lia. rewrite alu_and. unfold v_and.
        rewrite !u_small by lia. rewrite land_pagemask by lia.
        rewrite <- Zplus_mod_idemp_l, Haral. change ((0 + 24) mod 4096)%Z with 24%Z. f_equal. lia. }
      unfold kn_H, kn_Hstack, kn_Hheap, kn_Himage, know_ok. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil.
      all: cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off];
           rewrite ?AREA; rewrite ?AX by lia; rewrite ?SPX; cbn [edenot]; rewrite ?E0, ?E1, ?E2, ?E3, ?E4, ?E5, ?E8, ?E41, ?E42;
           rewrite ?(u_small area) by lia; rewrite ?Z.add_0_r;
           change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite ?Z.add_0_l.
      (* [comment removed for export] *)
      all: try (split; [lia | first [exact Hspa | exact Haral | exact Hgmal]]; fail).
      all: lazymatch goal with
           (* [comment removed for export] *)
           | |- (_ <= _ <= _)%Z => lia
           | |- (_ <= _)%Z \/ (_ <= _)%Z => lia
           (* [comment removed for export] *)
           | |- (0 <= _)%Z /\ (_ <= 2 ^ 64)%Z /\ (forall i, _ -> M0 (Z_to_bv 64 i) = None) =>
               split; [lia|]; split; [lia|]; intros i Hi; (eapply Himg; [ | exact Hi]);
               cbn; repeat (first [left; reflexivity | right])
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall d m, _ -> _ -> store_ok _ _ (Z_to_bv 64 (?B + d)) m = true) =>
                    split; [lia|]; intros d m Hd Hm;
                    first [ replace (B + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia; apply Hst; lia
                          | replace (B + d)%Z with (bv_unsigned gm + d)%Z by lia; apply Hgr; lia
                          | apply Hma; lia
                          | replace (B + d)%Z with (0x20000 + d)%Z by lia; apply data_store_ok; lia ]
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall i, _ -> M0 _ = Some (Z_to_bv 8 0)) =>
                    split; [rewrite ?u_small by lia; lia|]; intros i Hi; rewrite ?u_small in Hi by lia;
                    apply Hgend; lia
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ _ 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 _)) =>
                    split; [lia|]; split; [lia|]; cbn [rdn];
                    first [rewrite Hgzr | rewrite Hge5 | rewrite Hpm4 | rewrite Hpm3]; reflexivity
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ (Z_to_bv 64 ?A) _ = _ =>
                    split; [lia|]; split; [lia|]; unfold cell in *; rewrite ?Z_to_bv_bv_unsigned in *;
                    let try1 H := (lazymatch type of H with rdn _ _ (Z_to_bv 64 ?A2) _ = _ =>
                                     replace A with A2 by (clear; lia); exact H end) in
                    first [ exact Hgmeta | try1 Hpm2 | try1 Hra | try1 Hf64 | try1 Hf72 | try1 Hf80 | try1 Hf88 | try1 Hf96 | try1 Hf104 | try1 Hf112
                          | try1 Hf120
                          | try1 Hgmeta | try1 Hghdr | try1 Hge4 | try1 Hck | try1 Hgp | try1 Hgn | try1 Hgmm
                          | try1 Hgav | try1 Hgfr | try1 HgW | try1 Hsec | try1 Hfmh | try1 Hact | try1 Hus | try1 Hseq
                          | try1 Hinit | try1 Hctr | try1 Ham | try1 Hamc | try1 Hamac | try1 Hmah | try1 Hmat | try1 Hamas
                          | try1 Hself | try1 Hpgs
                          | try1 Htc | try1 Herr' | try1 Hgd ]
                end).
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_know_short : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (length content < 6)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_short.
  Proof using .
    intros e HK Hlt. unfold kn_short. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|constructor]. apply krange_intro.
    change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
  Qed.

  Lemma content_byte : forall j, (j < length content)%nat ->
    rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + 32 + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof using HP.
    intros j Hj. pose proof (hp_gm _ _ _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ _ _ HP) as HL.
    pose proof (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP) as Hsp0.
    pose proof (hp_content _ _ _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (rdn_nth RSEGS M0 (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma hdr_know_long : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (6 <= length content)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_long.
  Proof using HP.
    intros e HK Hge. pose proof (hp_gm _ _ _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ _ _ HP) as HL.
    pose proof (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP) as Hsp0.
    pose proof (hp_content _ _ _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (u64_range gm) as Ugm.
    pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
    change (bv_modulus 8) with 256%Z in B0, B1.
    unfold kn_long. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|constructor]]]]].
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + Z.of_nat 0)%Z by lia. apply content_byte. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      replace (bv_unsigned gm + 33)%Z with (bv_unsigned gm + 32 + Z.of_nat 1)%Z by lia. apply content_byte. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 6)) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      rewrite u_small by lia. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 7)) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof using . reflexivity. Qed.

  Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x103bf) 31 = Some msg_short.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x102f2) 31 = Some msg_overrun.
  Proof using . vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hp_facts :
    ((0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z)
    /\ ((0x52000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned gm mod 4096 = 0)%Z)
    /\ (0 < bv_unsigned tid < 2 ^ 22)%Z /\ (Z.of_nat (length content) < 65536)%Z.
  Proof using HP.
    split; [exact (hp_sp0 _ _ _ _ _ _ _ _ _ _ HP)|]. split; [exact (hp_gm _ _ _ _ _ _ _ _ _ _ HP)|].
    split; [exact (hp_tid _ _ _ _ _ _ _ _ _ _ HP) | exact (hp_L _ _ _ _ _ _ _ _ _ _ HP)].
  Qed.

  (* [comment removed for export] *)
  Definition err_tail_stmt (sr : list expr) (kn : list kentry) : Prop :=
    forall vals R M,
      length vals = 75%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 3 = gm -> vals_ev vals 4 = tid ->
      regs_ok (ENVh content vals) sr R -> know_ok RSEGS (ENVh content vals) M kn ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x18d54) M (seg_rom RSEGS)) modelh)
                 (t_exit (exit_code 2) fs0).

  Ltac err_tail_1 HL P0 P3 P4 HR HK :=
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL);
    pose proof (u64_range gm) as Ugm;
    (* [comment removed for export] *)
    run_block scr0 75%nat;
    (* [comment removed for export] *)
    eapply (rz_munmap RSEGS _ _ _ modelh ECALLW gm 69632);
    [ vm_compute; reflexivity
    | apply is_ecall_ECALLW
    | reflexivity
    | reflexivity
    | regv HR (17 : reg); reflexivity
    | regv HR (10 : reg); cbn [edenot ev ENVh]; exact P3
    | exact GMA
    | regv HR (11 : reg); reflexivity
    | lia
    | change (page_round_up_Z 69632) with 69632%Z; unfold TASK_SIZE; lia
    | change (page_round_up_Z 69632) with 69632%Z; cbv [m_vmmaps modelh model_post mkModelC m_vm vmst_maps]; exact Hmap
    | ];
    rewrite v_addi_pc4 by lia; change (0x18770 + 4)%Z with 0x18774%Z;
    change (page_round_up_Z 69632) with 69632%Z.

  Ltac err_tail_2 HL P0 P3 P4 HR HK :=
    let HK2 := fresh "HK2" in let HR2 := fresh "HR2" in
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
      pose proof (know_ok_unfill RSEGS E Mc kn (EVar 3) 0 69632 HK
                    ltac:(apply flat_intro; cbn [edenot ev ENVh]; rewrite ?P3; lia) ltac:(lia)) as HK2;
      let kn' := eval vm_compute in (kn_unfill kn (EVar 3) 0 69632) in
      change (kn_unfill kn (EVar 3) 0 69632) with kn' in HK2
    end;
    unfold adenot, v_addi in HK2; cbn [a_base a_off edenot ev ENVh] in HK2;
    rewrite P3, Z.add_0_r, Z_to_bv_bv_unsigned in HK2;
    clear HK; rename HK2 into HK;
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end;
    clear HR; rename HR2 into HR;
    (* [comment removed for export] *)
    run_block scr0 75%nat.

  Ltac err_tail_3 HL P0 P3 P4 HR HK :=
    let Hst := fresh "Hst" in let Ktid := fresh "Ktid" in
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255))
                                                  (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)))));
    [ | replace (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)) with fs0 by reflexivity;
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 4)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENVh] in Ktid; rewrite P4 in Ktid
    end;
    exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x309e8), (bv_unsigned tid),
           (Z_to_bv 64 0x510b8), (Z_to_bv 64 0);
    split; [|split; [reflexivity|split; [reflexivity|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        lazymatch type of HK with know_ok _ ?E _ ?kn =>
          pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVh] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | lia
      | lit_u; change (199144 - 168)%Z with 0x30940%Z;
        let Htc := fresh in krd HK 0x30940%Z 4%nat Htc; rewrite Htc; cbn [ev ENVh]; rewrite P4;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK | krd_solve HK | left; unfold ax_empty; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ].

  Ltac err_tail_tac :=
    intros vals R M HL P0 P3 P4 HR HK;
    err_tail_1 HL P0 P3 P4 HR HK;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_2 HL P0 P3 P4 HR' HK' end;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_3 HL P0 P3 P4 HR' HK' end.

  Lemma err_tail_short : err_tail_stmt srSB0 knSB0.
  Proof using HP Hmap. err_tail_tac. Qed.

  Lemma err_tail_overrun : err_tail_stmt srOB0 knOB0.
  Proof using HP Hmap. err_tail_tac. Qed.

  (* [comment removed for export] *)
  Ltac usmall_off := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?x + ?k))] => rewrite (u_small (bv_unsigned x + k)) by lia end.

  (* [comment removed for export] *)
  Ltac stdio_then_tail vals res msg msg_img msg_addr TAIL HL P0 P3 P4 HR HK :=
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
    unfold t_die, W;
    apply (stdio_call_sound vals (blobs_ev [content]) sr kn Rc Mc modelh res [] msg
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) ltac:(vm_compute; reflexivity)));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      try (replace (Z.of_nat (@length byte msg)) with 31%Z by reflexivity); cbn [length Z.of_nat];
    [ cbn [edenot]; lia
    | cbn [edenot]; lia
    | cbn [edenot]; lit_u; reflexivity
    | pose proof rw_bytes_max_ge17; lia
    | lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia
    | reflexivity
    | cbn [edenot]; replace (@length byte msg) with 31%nat by reflexivity;
      rewrite (kimg_rdn RSEGS (ENVh content vals) _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
                 _ _ msg_addr 31 HK eq_refl) by (cbn; lia);
      apply msg_img
    | apply fds_std_2
    | reflexivity
    | reflexivity
    | apply t_exit_has_nil
    | clear HR HK;
      let R' := fresh "R" in let M' := fresh "M" in let HR' := fresh "HR" in let HK' := fresh "HK" in
      intros R' M' HR' HK';
      apply (TAIL (vals ++ junk_vals R') R' M');
      [ rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P3
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P4
      | exact HR' | exact HK' ] ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_short : (length content < 6)%nat ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x12b84) M0 (seg_rom RSEGS)) modelh) (t_die msg_short fs0).
  Proof using HP Hmap.
    intros Hlt. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_short e HK0 Hlt) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr0 43%nat.
    (* [comment removed for export] *)
    stdio_then_tail vals scS msg_short msg_short_img 0x103bf%Z err_tail_short HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_overrun :
    (6 <= length content)%nat -> (Z.of_nat (length content) < 6 + hdr_cfglen content)%Z ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x12b84) M0 (seg_rom RSEGS)) modelh) (t_die msg_overrun fs0).
  Proof using HP Hmap.
    intros Hge Hov. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_long e HK0 Hge) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (hdr_cfglen_range content) as CR. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr_taken 43%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. fold cfglen_x. cbn [edenot].
      rewrite (cfglen_val content vals P6 P7). change (ev (ENVh content vals) 5) with (vals_ev vals 5). rewrite P5.
      rewrite alu_add. unfold v_add. cbn [branch_taken]. unfold bv_ltu.
      rewrite (u_small (hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      rewrite !u_small by lia. apply Z.ltb_lt. lia. }
    (* [comment removed for export] *)
    stdio_then_tail vals scO msg_overrun msg_overrun_img 0x102f2%Z err_tail_overrun HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_ok : forall brkv mas K,
    world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M0 ->
    (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
    (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                              content R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12d58) M' (seg_rom RSEGS)) modelh) K) ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x12b84) M0 (seg_rom RSEGS)) modelh) K.
  Proof using HP.
    intros brkv mas K W0 Hok HK_T. destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_cfglen_range content) as CR.
    pose proof (hdr_know_long e HK0 ltac:(lia)) as HK. clear HK0.
    pose proof hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (u64_range gm) as Ugm. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    (* [comment removed for export] *)
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL : length (valsh e) = 43%nat) by (unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    (* [comment removed for export] *)
    pose proof (env_app_regs (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_H R0
                  ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M0 kn_long
                  ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsh e ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PB43 : vals_ev vals 43 = cb 1%nat).
    { unfold vals. replace 43%nat with (length (valsh e) + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 44 = cb 0%nat).
    { unfold vals. replace 44%nat with (length (valsh e) + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB45 : vals_ev vals 45 = cb 2%nat).
    { unfold vals. replace 45%nat with (length (valsh e) + 2)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB46 : vals_ev vals 46 = cb 3%nat).
    { unfold vals. replace 46%nat with (length (valsh e) + 3)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    (* [comment removed for export] *)
    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z
        with (bv_unsigned gm + 32 + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by lia.
      rewrite content_byte by lia. rewrite w2le1_byte. reflexivity. }
    (* [comment removed for export] *)
    run_block_keep scr_fall 43%nat.
    all: try (unfold sc_denot; fold cfglen_x).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- branch_taken _ _ _ = false =>
                  cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5;
                  rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                  rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                  rewrite !u_small by lia; apply Z.ltb_ge; lia
              end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- exists bs, rdn _ _ (adenot _ (SA _ ?k)) 1 = Some bs /\ _ =>
                  let i := eval vm_compute in (Z.to_nat (k - 34)) in
                  eexists; split;
                  [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                    change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                    rewrite alu_add; unfold v_add;
                    rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia;
                    replace (bv_unsigned gm + hdr_cfglen content + k)%Z
                      with (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z by lia;
                    apply (CB i); lia
                  | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                    first [rewrite PB43 | rewrite PB44 | rewrite PB45 | rewrite PB46];
                    unfold cb, extz; cbn [lez bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
              | |- flat _ (SA _ ?k) _ =>
                  unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                  change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                  rewrite alu_add; unfold v_add; rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia; lia
              end).
    all: let n := numgoals in idtac "after-block goals:" n.
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T.
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hgm Har Hai Hdj Htid HLL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hinit Hctr Hfmh Ham Hamc Hamac Hmah Hmat Hamas Hact Hus Hseq Htc Herr
                    Hself Hgd Hpgs Himg].
    assert (A38 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) cfglen_x) (ELit 38))
                  = Z_to_bv 64 (bv_unsigned gm + 38 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add. unfold v_add. rewrite (alu_add gm). unfold v_add. rewrite (u_small (hdr_cfglen content)) by lia.
      rewrite (u_small (bv_unsigned gm + hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 38)) with 38%Z. f_equal. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 5) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite (Z.mod_small L), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (L + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (L + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen, L. lia. }
    constructor.
    all: try (regv HR (1 : reg); reflexivity).
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0. f_equal; lia.
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (11 : reg). exact CV.
    - regv HR (12 : reg). exact A38.
    - regv HR (13 : reg). exact APL.
    - regv HR (8 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (9 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (18 : reg). exact CV.
    - regv HR (19 : reg). exact A38.
    - regv HR (20 : reg). exact APL.
    - regv HR (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - regv HR (22 : reg). reflexivity.
    - regv HR (23 : reg). reflexivity.
    - exact Hsp.
    - lia.
    - unfold L in *. lia.
    - exact Hst.
    - constructor; assumption.
    - exact W0.
    - exact Hcont.
  Qed.

End Header.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_of_defined : forall M (a : Z) (m : nat),
  (0 <= a)%Z -> (a + Z.of_nat m <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat m)%Z -> M (Z_to_bv 64 i) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof using .
  intros M a m Ha Hm Hdef. destruct m as [|m]; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x) Hx). rewrite Z_to_bv_bv_unsigned in Hdef.
  destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof using .
  induction l as [|[b k] l IH]; intros a n Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as -> ->. apply map_has_head.
  - apply map_has_cons. apply IH. exact Hin.
Qed.

Lemma zbv_add1 : forall A, (0 <= A)%Z -> (A + 1 < 2 ^ 64)%Z -> Z_to_bv 64 A + 1 = Z_to_bv 64 (A + 1).
Proof using . intros A H0 H1. rewrite w_add_1, u_small by lia. reflexivity. Qed.

Section Intro.
  Variables (sp0 p1 gm tid sec cnr : word) (area brkv mas : Z) (content : list byte).
  Variables (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis RP : read_post0 sp0 p1 gm content Rr Mr R M.
  Hypothesis W0 : world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) M.
  Hypothesis MF : main_frame (bv_unsigned sp0) M.
  Hypothesis Htop : (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z.
  Hypothesis HL : (Z.of_nat (length content) < 65536)%Z.

  Lemma header_pre_intro : header_pre sp0 p1 gm tid sec cnr area content R M.
  Proof using HL Htop Hvsp MF RP W0.
    destruct RP as [Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs6 Qs7 Qkeep Qframe Qgrows Qcontent Qstack Qgroup].
    pose proof W0 as W.
    destruct W as [Wsecret Winit Wctr Wfmh Wam Wamc Wamac Wmas Wmah Wmat Wamas Wactive44 Wusage44 Wseq Wbrk
                   Wachk Wanext Wans Wsprev Wsnext Wsmem Wsmsk WsW Warest Wadef Wgmeta Wgaidx Wgpad Wenf Wgtail Wgdef
                   Waal Wgmal Warng Waimg Wgmrng Wdisj Wbrkv Wmasv Wtid Wtidr Werrno Wself Wcanary Wpagesz Wimg].
    destruct MF as [F1 F2 F3 F4 F5 F6 F7 F8 F9].
    pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp.
    destruct Hvsp as (SPlo & SPhi & SPal). unfold sp_window_lo, sp_window_hi in *.
    rewrite ctx_active_44 in Wactive44. rewrite ctx_usage_44 in Wusage44. rewrite W64K_val in WsW.
    unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count,
      ctx_avail_meta_area_count, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas, ctx_seq, CTX
      in Wsecret, Winit, Wctr, Wfmh, Wam, Wamc, Wamac, Wmah, Wmat, Wamas, Wseq.
    (* [comment removed for export] *)
    destruct Wenf as [Pp Pe Pr_ Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. subst Pp Pe Pr_ Pq.
    constructor.
    - exact Qsp. - exact Qgp. - exact Qtp. - exact Qs0. - exact Qs1. - exact Qs2. - exact Qs3. - exact Qs4. - exact Qs5.
    - exact Qs6. - exact Qs7.
    - split; [lia | exact SPal].
    - repeat split; first [lia | exact Wgmal].
    - repeat split; first [lia | exact Waal].
    - exact Waimg.
    - exact Wdisj.
    - exact Wtidr.
    - exact HL.
    - exact Qstack.
    - exact F1. - exact F2. - exact F3. - exact F4. - exact F5. - exact F6. - exact F7. - exact F8. - exact F9.
    - exact Qgroup.
    - exact Wgmeta.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 28)%Z with (bv_unsigned gm + 16 + 16 * 1 - 4)%Z by lia. exact Pm4.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 29)%Z with (bv_unsigned gm + 16 + 16 * 1 - 3)%Z by lia. rewrite Pm3. reflexivity.
    - (* [comment removed for export] *)
      unfold cell. replace (bv_unsigned gm + 30)%Z with (bv_unsigned gm + 16 + 16 * 1 - 2)%Z by lia. rewrite Pm2. reflexivity.
    - (* [comment removed for export] *) replace (bv_unsigned gm + 65568)%Z with (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z by lia. apply Pzr. lia.
    - replace (bv_unsigned gm + 69623)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z by lia. apply Pe5. lia.
    - unfold cell. replace (bv_unsigned gm + 69624)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z by lia.
      rewrite (Pe4 ltac:(lia)). reflexivity.
    - exact Wgtail.
    - exact Qcontent.
    - (* [comment removed for export] *)
      intros d m Hd Hm. apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      replace i with (area + (i - area))%Z by lia. apply Wadef. lia.
    - exact Wachk.
    - exact Wsprev.
    - exact Wsnext.
    - exact Wsmem.
    - (* [comment removed for export] *)
      unfold cell in *. exact (rdn_firstn RSEGS M 8 _ _ 4 Wsmsk ltac:(lia)).
    - unfold cell in *.
      pose proof (rdn_skipn RSEGS M 8 (Z_to_bv 64 (area + 48)) _ 4 Wsmsk ltac:(lia)) as H4.
      rewrite w_add_nat, u_small in H4 by lia.
      replace (area + 52)%Z with (area + 48 + Z.of_nat 4)%Z by lia. exact H4.
    - exact WsW.
    - exact Wsecret. - exact Winit. - exact Wctr. - exact Wfmh. - exact Wam. - exact Wamc. - exact Wamac.
    - exact Wmah. - exact Wmat. - exact Wamas.
    - exact Wactive44.
    - exact Wusage44.
    - exact Wseq.
    - exact Wtid.
    - exact Werrno.
    - exact Wself.
    - exact Wcanary.
    - exact Wpagesz.
    - (* [comment removed for export] *)
      intros lo hi i Hin Hi.
      apply (proj1 (Forall_forall _ _) Wimg (lo, hi) Hin). exact Hi.
  Qed.
End Intro.

(* [comment removed for export] *)
Lemma in_rng_lit : forall (i base : Z) (len : Z),
  (0 <= base < 2 ^ 64)%Z -> (0 <= i < 2 ^ 64)%Z ->
  in_rng (Z_to_bv 64 i) (Z_to_bv 64 base) len <-> (base <= i < base + len)%Z.
Proof using . intros i base len Hb Hi. unfold in_rng. rewrite !u_small by lia. tauto. Qed.

Lemma read0_outside : forall (sp0 gm : word) (L i : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z -> (0 <= L)%Z -> (0 <= i < 2 ^ 64)%Z ->
  (bv_unsigned gm + 32 + L < 2 ^ 64)%Z ->
  ~ (bv_unsigned sp0 - 8388608 <= i < bv_unsigned sp0 - 128)%Z ->
  ~ (0x208d9 <= i < 0x308d9)%Z ->
  ~ (bv_unsigned gm + 32 <= i < bv_unsigned gm + 32 + L)%Z ->
  outside (Z_to_bv 64 i) (read_regions0 sp0 gm L).
Proof using .
  intros sp0 gm L i Hsp HL Hi Hgl N1 N2 N3. unfold read_regions0. cbn [outside].
  pose proof (u64_range gm).
  rewrite !in_rng_lit by lia. repeat split; lia.
Qed.

Lemma world0_after_read0 : forall (sp0 p1 gm : word) (content : list byte) (Rr : bvmap 5 word) (Mr : word -> option byte)
    (R : bvmap 5 word) (M : word -> option byte) (area brkv mas tid sec cnr : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid sec cnr Mr ->
  world0 area (bv_unsigned gm) brkv mas tid sec cnr M.
Proof using .
  intros sp0 p1 gm content Rr Mr R M area brkv mas tid sec cnr Hsp RQ HL Htop W.
  pose proof (w_area_rng _ _ _ _ _ _ _ _ W) as Har. pose proof (w_area_img _ _ _ _ _ _ _ _ W) as Hai.
  pose proof (w_gm_rng _ _ _ _ _ _ _ _ W) as Hgr. pose proof (w_disj _ _ _ _ _ _ _ _ W) as Hdj.
  pose proof (w_grp_def _ _ _ _ _ _ _ _ W) as Hdef.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (rq_grows _ _ _ _ _ _ _ _ RQ) as Hgw.
  pose proof (u64_range gm) as Ugm.
  eapply world0_frame; [exact W | |].
  - intros i Hi. apply Hfr. unfold world0_fp in Hi. apply read0_outside; lia.
  - intros i Hi. apply Hgw. apply Hdef. exact Hi.
Qed.

Lemma main_frame_after_read0 : forall (sp0 p1 gm : word) (content : list byte) (Rr : bvmap 5 word) (Mr : word -> option byte)
    (R : bvmap 5 word) (M : word -> option byte),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  main_frame (bv_unsigned sp0) Mr -> main_frame (bv_unsigned sp0) M.
Proof using .
  intros sp0 p1 gm content Rr Mr R M Hsp RQ HL Htop MF.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (u64_range gm) as Ugm.
  eapply main_frame_frame; [lia | lia | | exact MF].
  intros i Hi. apply Hfr. apply read0_outside; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem header_phase {AMB : Amb} : forall (sp0 p1 gm tid sec cnr : word) (area brkv mas : Z) (content : list byte)
    (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs)
    (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte),
  valid_sp sp0 ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr) Mr ->
  main_frame (bv_unsigned sp0) Mr ->
  (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  (Z.of_nat (length content) < 65536)%Z ->
  In (gm, Z_to_bv 64 69632) (vm_maps VM) ->
  (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned sec) (bv_unsigned cnr)
                            content R' M' ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12d58) M' (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
                (t_target content fs0)) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
             (t_body content fs0).
Proof using .
  intros sp0 p1 gm tid sec cnr area brkv mas content VM stdin0 fs0 Rr Mr R M Hvsp RP W0r MFr Htop HL Hin HT.
  assert (Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z)
    by (destruct Hvsp as (SPlo & SPhi & _); unfold sp_window_lo, sp_window_hi in *; lia).
  pose proof (world0_after_read0 sp0 p1 gm content Rr Mr R M area brkv mas _ _ _ Hsp RP HL Htop W0r) as W0.
  pose proof (main_frame_after_read0 sp0 p1 gm content Rr Mr R M Hsp RP HL Htop MFr) as MF.
  pose proof (header_pre_intro sp0 p1 gm tid sec cnr area brkv mas content Rr Mr R M Hvsp RP W0 MF Htop HL) as HP.
  pose proof (map_has_In _ _ _ Hin) as Hmap.
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as CR.
  unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length content))%Z eqn:E1; [apply Z.leb_le in E1; unfold MAX_INPUT in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2.
  - apply Nat.ltb_lt in E2. apply (header_short sp0 p1 gm tid sec cnr area content VM stdin0 fs0 R M HP Hmap E2).
  - apply Nat.ltb_ge in E2.
    destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
               256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3.
    + apply Nat.ltb_lt in E3.
      apply (header_overrun sp0 p1 gm tid sec cnr area content VM stdin0 fs0 R M HP Hmap E2).
      unfold hdr_cfglen, hdr_cfg, hdr_b0, hdr_b1 in *. lia.
    + apply Nat.ltb_ge in E3.
      pose proof (t_body_target content fs0 ltac:(unfold MAX_INPUT; lia) ltac:(unfold hdr_cfg, hdr_b0, hdr_b1; lia)) as TB.
      unfold t_body in TB. rewrite E1 in TB.
      replace (length content <? 6)%nat with false in TB by (symmetry; apply Nat.ltb_ge; lia).
      replace (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
               256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat with false in TB
        by (symmetry; apply Nat.ltb_ge; lia).
      rewrite TB.
      apply (header_ok sp0 p1 gm tid sec cnr area content VM stdin0 fs0 R M HP brkv mas _ W0); [|exact HT].
      unfold hdr_cfglen, hdr_cfg, hdr_b0, hdr_b1 in *. lia.
Qed.
End WithFP1.


