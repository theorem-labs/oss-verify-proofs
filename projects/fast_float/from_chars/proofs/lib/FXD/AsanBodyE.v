(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanTblAll.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanTblH2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TBLH : tree xi := AsanTblAll.TBLA.      (* [comment removed for export] *)
Fixpoint mk_img_runsH (rs : list (Z * nat)) (acc : tree Z) : tree Z :=
  match rs with [] => acc | (lo, n) :: rs' => mk_img_runsH rs' (mk_img_acc ASEGS n (Z.shiftr lo 3) acc) end.
Definition IMGH : tree Z := mk_img_runsH (H_WR ++ S0M_WR) TEmpty.
Lemma TBLH_ok : tbl_ok ASEGS TBLH. Proof. exact AsanTblAll.TBLA_ok. Qed.
Lemma TBLH_ecall : ecall_ok ASEGS TBLH. Proof. exact AsanTblAll.TBLA_ecall. Qed.
Lemma mk_img_runsH_ok : forall rs t, Forall (fun p => 0 <= fst p) rs -> img_ok ASEGS t -> img_ok ASEGS (mk_img_runsH rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Hrs Ht; cbn [mk_img_runsH]; [exact Ht|].
  inversion Hrs as [|? ? Hp Hrs']; subst. apply IH; [exact Hrs'|]. apply mk_img_acc_ok; [|exact Ht].
  cbn [fst] in Hp. apply Z.shiftr_nonneg. exact Hp.
Qed.
Lemma IMGH_ok : img_ok ASEGS IMGH.
Proof.
  apply mk_img_runsH_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) (H_WR ++ S0M_WR) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.

Definition F60000 : nat := 60000.
(* [comment removed for export] *)
Definition STOPS_H : list Z := [0xd84a4; 0xb84f4; 0x60ef0; 0x8fe88; 0x8fe60;
                                0x52e0c; 0x639e0; 0x82914; 0x81f88; 0x73c44; 0xd3954; 0xca390; 0xc4798].
Definition P_H : plan := PRun F60000 STOPS_H [].
Definition P_RETRY : plan := PRun F3000 [0xca418; 0xca39c] [].
(* [comment removed for export] *)
Definition F0W : wsrc := WBuf (lconst 0x638690) BPre 0.
Definition F1W : wsrc := WLit 0x14c9f.
Definition P_RETRY2 : plan := PRun F3000 [0xca418; 0xca39c; 0xca458] [].
(* [comment removed for export] *)
Definition WBL1 : MCP := MWritevL 1 F0W F1W (MAlt MVoid (MSegK 20 P_RETRY2 (KCons 0xca39c 0 (MPop MEnd) KNil))).
Definition KWL (k : MCP) : MCP :=
  MJoin (MWritevL 1 F0W F1W (MAlt MVoid (MSegK 20 P_RETRY2 (KCons 0xca418 66 WBL1 (KCons 0xca39c 0 (MPop MEnd) KNil))))) 0xca39c k.
(* [comment removed for export] *)
Definition WBF : MCP := MWritev2 (lconst 0x638690) (MSegK 20 P_RETRY (KCons 0xca418 66 MEnd (KCons 0xca39c 0 MEnd KNil))).
Definition WBF1 : MCP := MWritev2 (lconst 0x638690) (MAlt MVoid (MSegK 20 P_RETRY (KCons 0xca39c 0 (MPop MEnd) KNil))).
Definition KWF (n : nat) (k : MCP) : MCP :=
  match n with
  | Datatypes.S (Datatypes.S O) => MJoin (MWritev2 (lconst 0x638690) (MAlt MVoid (MSegK 20 P_RETRY (KCons 0xca418 66 WBF1 (KCons 0xca39c 0 (MPop MEnd) KNil))))) 0xca39c k
  | _ => MJoin (MWritev2 (lconst 0x638690) (MSegK 20 P_RETRY (KCons 0xca418 66 (MLoopW 22 WBF (KCons 0xca39c 0 (MPop MEnd) KNil)) (KCons 0xca39c 0 (MPop MEnd) KNil)))) 0xca39c k
  end.
(* [comment removed for export] *)
Definition KF5N (n : nat) : MCP := MSegK 40 (jplanF 8) (KCons 0xca390 66 (KWF n (MSegK 40 (jplanF 8) (KCons 0xc4798 94 MExit KNil))) (KCons 0xc4798 94 MExit KNil)).
Definition KF4N (n : nat) : MCP := MSegK 40 (jplanF 8) (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x40124 12))) (KF5N n)) KNil).
Definition KF3N (n : nat) : MCP := MSegK 40 (jplanFW 10) (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x40124 12))) (KF4N n)) KNil).
Definition KF2N (n : nat) : MCP := MSegK 40 (jplanFW 10) (KCons 0x81f88 0 (NPUT (KF3N n)) KNil).
(* [comment removed for export] *)
Definition TAILE (n : nat) : MCP := MConcR (MSegK 40 (jplanFW 10) (KCons 0x82914 0 (NUNW (MSegK 40 (jplanFW 10) (KCons 0x82914 0 (NUNW (KF2N n)) KNil))) KNil)).
(* [comment removed for export] *)
Fixpoint HRUN (k : nat) : MCP :=
  match k with
  | O => MEnd
  | Datatypes.S O => MSegK 20 P_H (KCons 0x8fe88 0 MEnd KNil)
  | Datatypes.S k' => MSegK 20 P_H (KCons 0x8fe60 0 (HRUN k') KNil)
  end.
(* [comment removed for export] *)
Definition KAFT (n : nat) : MCP :=
  match n with
  | Datatypes.S O => MSegK 20 P_H (KCons 0x8fe88 0 MEnd KNil)
  | Datatypes.S k => MSegK 20 P_H (KCons 0x8fe60 0 (HRUN k) KNil)
  | O => MEnd
  end.
(* [comment removed for export] *)
Definition HBE (n : nat) : MCP := MSegK 20 P_H (KCons 0xcb050 29 (MIoctl 1 0x5413 (MSegK 20 P_RETRY (KCons 0xca390 66 (KWL (KAFT n)) KNil))) KNil).
(* [comment removed for export] *)
Definition KHE (n : nat) : MCP := MSplitP 2 (MJoin (MSplitB (lvar 4) 0 0 (HBE n) (HBE n)) 0x8fe88 (TAILE n)).

(* [comment removed for export] *)
Definition KFIN : nat -> MCP := fun _ => MEnd.
Definition JH (n : nat) (k : MCP) : MCP := MJoinS k 0x8fe60 (CALLS n) (KHE n).
Definition JBODY : MCP := JH 4 (JH 3 (JH 2 (JH 1 (KRDJBK KFIN KFIN)))).
Definition MAINWFJ : MCP :=
  TOPK (MSegK 20 P_OPEN (KCons 0xd3954 56 (MOpen MEnd
    (MSegK 20 P_MAL_U (KCons 0x82914 0 (NUNW
      (MSegK 20 P_TO_MMAP1 (KCons 0x73c44 222 (MCall (inl (A1 (NNullA 0x12000 GE true true false))) (MSep (TSepW 0 12) (MSep (TSepR 0 0x10000 0x63a000)
        (MSegK 20 P_TO_MMAP (KCons 0x73c44 222 (MCall (inl (A1 (NFixA 0x20000 11)))
          (MSegK 20 P_TO_PUT (KCons 0x81f88 0 (NPUT
            (MSegK 20 P_TO_READ (KCons 0xd3954 63 (MReadH IBR 0x10 6 JBODY MEnd) (KCons 0x3febc 0 MVoid KNil)))) (KCons 0x3febc 0 MVoid KNil))))
        (KCons 0x44360 0 MVoid KNil)))))) KNil))) (KCons 0x8fd58 0 MVoid KNil)))) (KCons 0x8fc60 0 MVoid KNil))).

(* [comment removed for export] *)
Definition mainwfj_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLH IMGH PV 6 65535 false (Some H0) apostF anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] [] MAINWFJ S1WF M1c FSClosed SHWF A1c.
Definition mainwfj_chk : bool := is_some mainwfj_res.
