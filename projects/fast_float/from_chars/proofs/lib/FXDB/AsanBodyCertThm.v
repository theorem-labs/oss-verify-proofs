(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam2Ok AcFam3 AcFam3Ok AcMALlib AcShmRd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPrefixG AsanPrefixLg AsanPrefixGL AsanBodyFam AsanBodyT.

Module AsanBodyTThm.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA0h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA2h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA3h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA4h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB0h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB1h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB2h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB3h OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB4h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafA1h.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhLeafB0p.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA0p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA1p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA2p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA3p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafA1h.AsanPhLeafA4p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB1p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB2p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB3p OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhLeafB0p.AsanPhLeafB4p.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcFam3Ok AcMALlib AcShmRd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyFam AsanBodyT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT.AsanBodyH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NB_G : positive := 13795%positive.
(* [comment removed for export] *)
Definition PHI : Z := 67108863.
Definition leaf_res (j : nat) (c : sst * smodel * fstate * shp * ast) : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLH IMGH PV 6 PHI false (Some H0) apostB anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS_T (MCont j NB_G)
    (fst (fst (fst (fst c)))) (snd (fst (fst (fst c)))) (snd (fst (fst c))) (snd (fst c)) (snd c).
(* [comment removed for export] *)
Definition LEAVES_T : list (nat * (sst * smodel * fstate * shp * ast)) :=
  [(1%nat, BLFA0h_C); (1%nat, BLFA1h_C); (3%nat, BLFA2h_C); (5%nat, BLFA3h_C); (7%nat, BLFA4h_C); (1%nat, BLFB0h_C); (1%nat, BLFB1h_C); (3%nat, BLFB2h_C); (5%nat, BLFB3h_C); (7%nat, BLFB4h_C);
   (0%nat, BLFA0p_C); (0%nat, BLFA1p_C); (2%nat, BLFA2p_C); (4%nat, BLFA3p_C); (6%nat, BLFA4p_C); (0%nat, BLFB0p_C); (0%nat, BLFB1p_C); (2%nat, BLFB2p_C); (4%nat, BLFB3p_C); (6%nat, BLFB4p_C)].
Definition leaves_chk : bool := forallb (fun jc => match leaf_res (fst jc) (snd jc) with Some [] => true | _ => false end) LEAVES_T.
Lemma leaves_cert : leaves_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Strategy opaque [TBLH IMGH mcheck].

Section T.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Let Hanode3 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc3 LIM) awf HA nk := alloc3_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf.
Variables (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp3 : path_is_dirref path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.
Hypothesis HFL : 6 <= Z.of_nat (length data0) <= PHI.

#[using="Type"] Lemma Hshm : forall model0 mem0 E S M ms model a, DEN ASEGS LIM model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.
Proof. LiaFast.lf_pins LiaFast.u0. exact (cls_shadow_readable LIM). Qed.

Definition cont_okR := cont_ok ASEGS cfg LIM PV path0 data0 fs0 argv0 false (Some H0) awf HA.

#[using="Hoff Hfs Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Theorem leaf_cont : Forall cont_okR CONTS_T -> forall jc, In jc LEAVES_T -> cont_okR (snd jc).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros HF [j c] Hin. cbn [snd].
  pose proof leaves_cert as Hc. unfold leaves_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc (j, c) Hin). cbn [fst snd] in Hc.
  destruct (leaf_res j c) as [[|x l]|] eqn:Hres; try discriminate. clear Hc.
  destruct c as [[[[S M] FS] sh] a]. unfold cont_okR, cont_ok. cbn [fst snd]. intros model0 mem0 E ms model Hd Hi HX Hw.
  unfold leaf_res in Hres. cbn [fst snd] in Hres.
  assert (Hcp : forall E M (a : ast) m0, HA E M a m0 -> Forall (sbytes_ok (sarg path0 argv0) E m0) (acopy_alloc a)) by (intros; constructor).
  assert (HC : forall j c, nth_error CONTS_T j = Some c -> cont_okR c).
  { intros j' c' Hj'. exact (proj1 (Forall_forall _ _) HF c' (nth_error_In _ _ Hj')). }
  exact (mchain_sound ASEGS cfg LIM TBLH IMGH A_wx A_segb Hoff Hfs A_respos A_reswf TBLH_ok IMGH_ok TBLH_ecall PV path0 data0 fs0 6 PHI argv0 false (Some H0)
            Hp1 Hp2 (fun _ => Hp3) Hp4 Hp5 (HFL_of _ _ _ HFL) ltac:(unfold PHI; lia) Hseg_asan apostB anil aeqb awf HA acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS_T
            alloc_awf_mono alloc_aeqb_eq alloc_HA_nil alloc_HA_agree (anodeB_ok cfg Hanode3 Hshm) Hcp HA_subst alloc_HA_mod (subs_nil_ok _) (subs_nil_use _) HC
            (MCont j NB_G) S M FS sh a [] Hres model0 mem0 E ms model Hd Hi HX Hw
            (fun S' M' FS' sh' a' model0' mem0' E' ms' model' Hin' => False_ind _ Hin')).
Qed.
End T.
(* [comment removed for export] *)
End AsanBodyTThm.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPrefixGSub.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPrefixGSub.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPrefixGLSub.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPrefixGLSub.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubE.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubE.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubL.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTailSubL AsanCallTE AsanCallTP AsanCallTL AsanBodyIf AsanBodyIfOk AsanBodyCertDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyHeadsP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyHeadsP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyHeadsP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanBodyHeadsP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT.AsanBodyH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixLg OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertThm.AsanBodyTThm OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanPrefixGLit OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGSub.AsanPrefixGCert OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGSub OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanPrefixGLLit OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGLSub.AsanPrefixGLCert OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixGLSub OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubE.AsanTailCertE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubP.AsanTailCertP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailTL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG.AsanTailFL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubL.AsanTailCertL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailSubL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyIf OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyIfOk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCertDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyHeadsP.AsanBodyCertS OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyHeadsP.AsanBodyHeadsE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyHeadsP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyHeadsP.AsanBodyHeadsL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Lemma some_inj1 : forall {A : Type} (a a' : A), Some a = Some a' -> a = a'.
Proof. intros A a a' H. inversion H. reflexivity. Qed.
Local Lemma some_inj4 : forall {A B C D : Type} (a a' : A) (b b' : B) (c c' : C) (d d' : D), Some (a, b, c, d) = Some (a', b', c', d') -> a = a' /\ b = b' /\ c = c' /\ d = d'.
Proof. intros A B C D a a' b b' c c' d d' H. inversion H. auto. Qed.

Strategy opaque [TBLH IMGH mcheck].

Section T.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
(* [comment removed for export] *)
Hypothesis Hharn : harn_hyps cfg.
Let Hanode2 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc2 LIM) awf HA nk := alloc2_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf.
Let Hanode3 : forall nk, anode_ok ASEGS cfg LIM (apost_alloc3 LIM) awf HA nk := alloc3_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf.
Variables (path0 : path) (data0 : list byte) (fs0 : Fs.Fs) (argv0 : list byte).
Hypothesis Hp1 : path_eqb path0 [] = false.
Hypothesis Hp2 : path_has_slash path0 = false.
Hypothesis Hp3 : path_is_dirref path0 = false.
Hypothesis Hp4 : (length path0 < path_max)%nat.
Hypothesis Hp5 : Forall (fun b => b <> Z_to_bv 8 0) path0.
Hypothesis HFL : 6 <= Z.of_nat (length data0) <= AsanBodyCertBase.PHI.

Notation cont_okB := (AsanBodyTThm.cont_okR cfg path0 data0 fs0 argv0).

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma nth_error_skip5 : forall {X : Type} (a b c d e : X) (l : list X) (j : nat), nth_error (app (cons a (cons b (cons c (cons d (cons e nil))))) l) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S j))))) = nth_error l j.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
Ltac sub_case Hj L := cbn [nth_error app] in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact L.
#[using="Hoff Hharn Hanode3"] Lemma subsXE_ok : forall j T MT aT fins, nth_error SUBS_XE j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hoff Hharn Hanode3 : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins Hj. unfold SUBS_XE, SUBT_E in Hj.
  do 5 (destruct j as [|j]; [sub_case Hj (taile_sub_ok cfg Hanode3 (cls_shadow_readable LIM))|]).
  rewrite nth_error_skip5 in Hj. exact (subsHE_okU cfg Hoff Hharn j T MT aT fins Hj).      (* [comment removed for export] *)
Qed.
#[using="Hoff Hharn Hanode2 Hanode3"] Lemma subsXP_ok : forall j T MT aT fins, nth_error SUBS_XP j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hoff Hharn Hanode2 Hanode3 : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins Hj. unfold SUBS_XP, SUBP_G, SUBT_P in Hj.
  do 2 (destruct j as [|j]; [sub_case Hj (pfing_sub_ok cfg Hanode2 (cls_shadow_readable LIM))|]).
  do 3 (destruct j as [|j]; [sub_case Hj (tailp_sub_ok cfg Hanode3 (cls_shadow_readable LIM))|]).
  rewrite nth_error_skip5 in Hj. exact (subsHP_okU cfg Hoff Hharn j T MT aT fins Hj).      (* [comment removed for export] *)
Qed.
#[using="Hoff Hharn Hanode2 Hanode3"] Lemma subsXL_ok : forall j T MT aT fins, nth_error SUBS_XL j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hoff Hharn Hanode2 Hanode3 : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins Hj. unfold SUBS_XL, SUBP_L, SUBT_L in Hj.
  do 2 (destruct j as [|j]; [sub_case Hj (pfinl_sub_ok cfg Hanode2 (cls_shadow_readable LIM))|]).
  do 3 (destruct j as [|j]; [sub_case Hj (taill_sub_ok cfg Hanode3 (cls_shadow_readable LIM))|]).
  rewrite nth_error_skip5 in Hj. exact (subsHL_okU cfg Hoff Hharn j T MT aT fins Hj).      (* [comment removed for export] *)
Qed.
#[using="Type"] Lemma subsNil_ok : forall j T MT aT fins, nth_error ([] : list sub_t) j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins LiaFast.u0. intros [|j] T MT aT fins H; discriminate H. Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Lemma body_sound : forall subs (Hsubs : forall j T MT aT fins, nth_error subs j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins) conts ch c,
  (forall j c', nth_error conts j = Some c' -> cont_okB c') -> body_res_s subs conts ch c = Some [] -> cont_okB c.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros subs Hsubs conts ch c HC Hres. destruct c as [[[[S M] FS] sh] a]. unfold AsanBodyTThm.cont_okR, cont_ok. cbn [fst snd].
  intros model0 mem0 E ms model Hd Hi HX Hw. unfold body_res_s in Hres. cbn [fst snd] in Hres.
  assert (Hcp : forall E M (a : ast) m0, HA E M a m0 -> Forall (sbytes_ok (sarg path0 argv0) E m0) (acopy_alloc a)) by (intros; constructor).
  exact (mchain_sound ASEGS cfg LIM TBLH IMGH A_wx A_segb Hoff Hfs A_respos A_reswf TBLH_ok IMGH_ok TBLH_ecall PV path0 data0 fs0 6 AsanBodyCertBase.PHI argv0 false (Some H0)
            Hp1 Hp2 (fun _ => Hp3) Hp4 Hp5 (HFL_of _ _ _ HFL) ltac:(unfold AsanBodyCertBase.PHI; lia) Hseg_asan apostX anil aeqb awf HA acopy_alloc asubst ag_ok alins_a aset_a amod_a subs conts
            alloc_awf_mono alloc_aeqb_eq alloc_HA_nil alloc_HA_agree (anodeX_ok cfg Hoff) Hcp HA_subst alloc_HA_mod Hsubs (fun _ => HA_subst_rev) HC
            ch S M FS sh a [] Hres model0 mem0 E ms model Hd Hi HX Hw
            (fun S' M' FS' sh' a' model0' mem0' E' ms' model' Hin' => False_ind _ Hin')).
Qed.
#[using="Type"] Lemma ok_nil_some : forall r, ok_nil r = true -> r = Some [].
Proof. LiaFast.lf_pins LiaFast.u0. intros [[|x l]|] H; try discriminate H. reflexivity. Qed.
#[using="Type"] Lemma no_conts : forall j c', nth_error ([] : list (sst * smodel * fstate * shp * ast)) j = Some c' -> cont_okB c'.
Proof. LiaFast.lf_pins LiaFast.u0. intros [|j] c' H; discriminate H. Qed.

#[using="Hoff Hfs Hharn Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Lemma contE : forall n, certHE n = true -> cont_okB (TE_C n).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0). intros n H. exact (body_sound _ subsXE_ok [] _ _ no_conts (ok_nil_some _ H)). Qed.
#[using="Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Lemma contPP : forall n, certHP n = true -> cont_okB (TPP_C n).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0). intros n H. exact (body_sound _ subsXP_ok [] _ _ no_conts (ok_nil_some _ H)). Qed.
#[using="Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Lemma contPL : forall n, certHL n = true -> cont_okB (TPL_C n).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0). intros n H. exact (body_sound _ subsXL_ok [] _ _ no_conts (ok_nil_some _ H)). Qed.
#[using="Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Lemma contP : forall n, certS n = true -> certHP n = true -> certHL n = true -> cont_okB (TP_C n).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  intros n HS HP HL. apply (body_sound _ subsNil_ok (CONTS_PL n) CH_S _); [|exact (ok_nil_some _ HS)].
  intros j c' Hj. destruct j as [|[|j]]; cbn [nth_error CONTS_PL] in Hj.
  - apply some_inj1 in Hj. destruct Hj. exact (contPP n HP).
  - apply some_inj1 in Hj. destruct Hj. exact (contPL n HL).
  - destruct j; discriminate Hj.
Qed.

#[using="data0 HFL"] Lemma all4 : forall f : nat -> bool, (f 1%nat && f 2%nat && f 3%nat && f 4%nat)%bool = true -> f 1%nat = true /\ f 2%nat = true /\ f 3%nat = true /\ f 4%nat = true.
Proof. LiaFast.lf_pins (fun (data0 HFL : LiaFast.U) => LiaFast.u0). intros f H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. tauto. Qed.

#[using="Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL"] Theorem body_conts : Forall cont_okB CONTS_T.
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hharn Hanode2 Hanode3 Hp1 Hp2 Hp3 Hp4 Hp5 HFL : LiaFast.U) => LiaFast.u0).
  destruct (all4 certS certS14) as (HS1 & HS2 & HS3 & HS4).
  destruct (all4 certHE certHE14) as (HE1 & HE2 & HE3 & HE4).
  destruct (all4 certHP certHP14) as (HP1 & HP2 & HP3 & HP4).
  destruct (all4 certHL certHL14) as (HL1 & HL2 & HL3 & HL4).
  unfold CONTS_T. repeat constructor.
  - exact (contP 1 HS1 HP1 HL1).
  - exact (contE 1 HE1).
  - exact (contP 2 HS2 HP2 HL2).
  - exact (contE 2 HE2).
  - exact (contP 3 HS3 HP3 HL3).
  - exact (contE 3 HE3).
  - exact (contP 4 HS4 HP4 HL4).
  - exact (contE 4 HE4).
Qed.
End T.
(* [comment removed for export] *)
