(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec RefLayout ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChSep FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxSNodes FxSFam FxCarve AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageThmT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanLayoutT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanLeafSpecT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanLeafSpecT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxCarve OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageThmT.AsanLeafLib OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLayoutT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafSpecT.AsanLeafSpec OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafSpecT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxChFamI AsanFamU AsanUsageT AsanUsageThmT AsanCoNFT.

Module AsanCoNFThmT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChAdd FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChSep FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblU.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode AsanQSites FxSNodes AsanSNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanPNodes FxSFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanSFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblU OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxDirConv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanUsageThmT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxChFamI AsanFamU AsanUsageT AsanUsageThmT AsanCoNFT AsanCoNFCertT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvG.FxOpenNF OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageThmT.AsanLeafLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanFamU OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageThmT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFCertT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Lemma pair_inj5 : forall {A B C D F : Type} (a a' : A) (b b' : B) (c c' : C) (d d' : D) (f f' : F), (a, b, c, d, f) = (a', b', c', d', f') -> a = a' /\ b = b' /\ c = c' /\ d = d' /\ f = f'.
Proof. intros A B C D F a a' b b' c c' d d' f f' H. inversion H. auto. Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_tl : forall mp (bs : list byte) a k, length bs = k -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (forall j, (j < length bs)%nat -> mp (woff a j) = Some (nth j bs (Z_to_bv 8 0))) ->
  read_cstr_aux mp a k = CstrTooLong.
Proof.
  intros mp bs. induction bs as [|b bs IH]; intros a k Hk Hnz Hm; destruct k as [|k]; cbn [length] in Hk; try lia; cbn [read_cstr_aux]; [reflexivity|].
  rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth].
  inversion Hnz as [|? ? Hb Hnz']; subst.
  destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [apply bv_eqb_eq in Eb; exfalso; exact (Hb Eb)|].
  rewrite woff_0. rewrite (IH (a + 1)%bv k ltac:(lia) Hnz'); [reflexivity|].
  intros j Hj. rewrite woff_succ. exact (Hm (Datatypes.S j) ltac:(cbn; lia)).
Qed.
Lemma cstr_access_len_tl : forall mp (bs : list byte) a k, length bs = k -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (forall j, (j < length bs)%nat -> mp (woff a j) = Some (nth j bs (Z_to_bv 8 0))) ->
  cstr_access_len_aux mp a k = k.
Proof.
  intros mp bs. induction bs as [|b bs IH]; intros a k Hk Hnz Hm; destruct k as [|k]; cbn [length] in Hk; try lia; cbn [cstr_access_len_aux]; [reflexivity|].
  rewrite <- (woff_0 a). rewrite (Hm O ltac:(cbn; lia)). cbn [nth].
  inversion Hnz as [|? ? Hb Hnz']; subst.
  destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [apply bv_eqb_eq in Eb; exfalso; exact (Hb Eb)|].
  rewrite woff_0. rewrite (IH (a + 1)%bv k ltac:(lia) Hnz'); [reflexivity|].
  intros j Hj. rewrite woff_succ. exact (Hm (Datatypes.S j) ltac:(cbn; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nf_case (fs0 : Fs.Fs) (p : list byte) : Prop :=
  (fs_lookup fs0 p = None /\ path_eqb p [] = false /\ path_has_slash p = false /\ path_is_dirref p = false /\ (length p < 4096)%nat) \/
  p = [] \/ (4096 <= length p)%nat.

Strategy opaque [TBLR IMGR mcheck].

Section NFTT.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Variables (fs0 : Fs.Fs) (p : list byte).
Hypothesis Hpl : Z.of_nat (length p) <= 131071.

Definition E1of (E : valu) : valu := upd E NNFT (Z_to_bv 64 (Z.of_nat (length p))).

(* [comment removed for export] *)
#[using="Type"] Lemma FSNF_wfT : Forall (fun g => fwf (s_next (bump TMAIN (Pos.succ NNFT))) g = true) FSNFT.
Proof. LiaFast.lf_pins LiaFast.u0. apply Forall_forall. intros g Hg. assert (H : forallb (fwf (s_next (bump TMAIN (Pos.succ NNFT)))) FSNFT = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. exact (H g Hg). Qed.
#[using="Type"] Lemma TMAIN_next : s_next TMAIN = NNFT. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Theorem den_conv_nfT : forall model0 mem0 E ms model, DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model -> Forall (fact_ok (E1of E)) FSNFT ->
  DEN ASEGS LIM model0 mem0 (E1of E) SNFT MMAIN ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 mem0 E ms model Hd HF. unfold SNFT.
  assert (Hd1 : DEN ASEGS LIM model0 mem0 (E1of E) TMAIN MMAIN ms model).
  { apply (den_agree ASEGS LIM model0 mem0 E (E1of E) TMAIN MMAIN ms model Hd). rewrite TMAIN_next. exact (agree_upd NNFT E _). }
  assert (Hd2 : DEN ASEGS LIM model0 mem0 (E1of E) (bump TMAIN (Pos.succ NNFT)) MMAIN ms model)
    by (apply den_bump; [exact Hd1 | rewrite TMAIN_next; lia]).
  apply den_add_facts; [exact Hd2|].
  pose proof FSNF_wfT as W. rewrite Forall_forall in W, HF |- *. intros g Hg. exact (conj (W g Hg) (HF g Hg)).
Qed.

#[using="Type"] Lemma SNF_next : s_next SNFT = Pos.succ NNFT. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma ANF_wf : awfUT (s_next SNFT) ANFT = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma SHNF_wf : shp_wf (s_next SNFT) SH_NFT = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma lpnf_wf : lwf (s_next S_OPT) LPNFT = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_pc : tlookup TBLR (s_pc S_OPT) = XEcall. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_a7 : a7c S_OPT = Some 56. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_a0 : arg S_OPT 0 = Some 18446744073709551516. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_a2 : arg S_OPT 2 = Some 32768. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_a1 : rget (s_regs S_OPT) (rkey a1r) = PV. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_fd : fd32 (Z_to_bv 64 18446744073709551516) = AT_FDCWD32. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_fl : Z.ldiff (bv_unsigned (Z_to_bv 64 32768)) open_ignored_flags = 0. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma S_OP_next : (s_next SNFT <= s_next S_OPT)%positive. Proof. LiaFast.lf_pins LiaFast.u0. apply Pos.leb_le. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma SHNF2_wfT : shp_wf (s_next TNFT) SH_NF2T = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma SHNF_wfT : shp_wf (s_next TNFT) SH_NFT = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma lpnf_wfT : lwf (s_next TNFT) LPNFT = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma TNF_next : s_next TNFT = Pos.succ (s_next S_OPT). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma SHNF2_den : forall E, shp_den PDUM fs0 p E SH_NF2T = shp_den PDUM fs0 p E SH_NFT.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E. unfold SH_NFT, SH_NF2T. cbn [shp_den List.map concat pend_evs pd_ch pd_off pd_src src_bytes].
  unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes].
  assert (H0' : Z.to_nat (uE E (lconst 0)) = O) by (unfold uE; rewrite lden_lconst; reflexivity).
  rewrite !H0'. f_equal. rewrite !app_nil_r, <- !map_app. rewrite !skipn_O. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hpl"] Lemma nf_path : forall model0 mem0 E S M ms model model1,
  DEN ASEGS LIM model0 mem0 E S M ms model -> DEN ASEGS LIM model0 mem0 E S M ms model1 ->
  HA3 (sarg PDUM p) E M (snd ANFT) mem0 -> uE E LPNFT = Z.of_nat (length p) ->
  nf_case fs0 p -> m_fs model0 = fs0 ->
  exists e, open_nf (m_fs model0) AT_FDCWD32 (read_cstr (in_mem (sys_input ASEGS (svc_set ms) (ms_reg ms 17))) (lden E PV)) e /\
    ranges_avoid (Hof E M model1) [(lden E PV, cstr_access_len_aux (in_mem (sys_input ASEGS (svc_set ms) (ms_reg ms 17))) (lden E PV) path_max)].
Proof. LiaFast.lf_pins (fun (Hpl : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E S M ms model model1 Hd Hd1 [Hs _] HLp Hcase Hfs0.
  unfold ANFT, sf_strs in Hs. cbn [snd] in Hs. cbn [fst] in Hs. apply Forall_cons_iff in Hs as [[Hc Hsb] _]. cbn [fst snd] in Hc, Hsb.
  destruct Hc as (C1 & C2 & C3 & C4). unfold sbytes_ok in Hsb. destruct Hsb as [Hlen Hby].
  set (B := uE E PV) in *. set (L := uE E LPNFT) in *. cbn [sarg] in Hby, Hlen.
  pose proof (uE_range E PV) as RB. fold B in RB.
  assert (HBL : B + L < wend B L) by (unfold wend; pose proof (Z.div_mod (B + L) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (Hmp : forall j, (j <= length p)%nat ->
            in_mem (sys_input ASEGS (svc_set ms) (ms_reg ms 17)) (woff (lden E PV) j) = Some (nth j (p ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  { intros j Hj. destruct (proj1 (C2 (B + Z.of_nat j) ltac:(lia))) as (q & Hq & Hqw).
    destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq _ Hqw) as (_ & _ & Hm).
    unfold woff. cbn [in_mem sys_input]. unfold ms_read_byte. cbn [svc_set ms_mem].
    replace (bv_unsigned (lden E PV)) with B by reflexivity. rewrite Hm.
    destruct (Nat.lt_ge_cases j (length p)) as [Hlt|Hge].
    - rewrite (Hby (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id, app_nth1 by lia. reflexivity.
    - assert (j = length p) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      rewrite <- Hlen. rewrite C4. reflexivity. }
  assert (Hnz : Forall (fun b => b <> Z_to_bv 8 0) p).
  { apply Forall_forall. intros b Hb. destruct (In_nth p b (Z_to_bv 8 0) Hb) as (k & Hk & Hkb).
    destruct (C3 (Z.of_nat k) ltac:(lia)) as (bb & Hbb & Hnzb). rewrite (Hby (Z.of_nat k) ltac:(lia)) in Hbb. rewrite Nat2Z.id, Hkb in Hbb.
    injection Hbb as ->. intros Hc. rewrite Hc in Hnzb. apply Hnzb. reflexivity. }
  assert (Hvis : forall k, 0 <= k <= L -> Hof E M model1 (woff (lden E PV) (Z.to_nat k)) = false).
  { intros k Hk. destruct (proj1 (C2 (B + k) ltac:(lia))) as (q & Hq & Hqw).
    destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd1 q Hq _ Hqw) as (Htp & _ & _).
    unfold woff. rewrite Z2Nat.id by lia. fold B. eapply frz_hidden_false; [exact Hd1 | exact Htp]. }
  destruct (Nat.lt_ge_cases (length p) 4096) as [Hsm|Hbig].
  - (* [comment removed for export] *)
    assert (Hk4 : (length p < path_max)%nat) by (unfold path_max; lia).
    exists ENOENT. split.
    + unfold read_cstr. rewrite (read_cstr_aux_ok _ p (lden E PV) path_max Hk4 Hnz Hmp).
      destruct Hcase as [(Hlk & Hne & Hsl & Hdr & _) | [-> | Hc']]; [|right; left; split; reflexivity | lia].
      left. split; [reflexivity|]. exists p. rewrite Hfs0. repeat split; first [reflexivity | assumption].
    + rewrite (FXC.FxChMain.cstr_access_len_ok PDUM [] PD4 _ p (lden E PV) path_max Hk4 Hnz Hmp).
      apply ranges_avoid_cons; [|apply ranges_avoid_nil]. intros k Hk.
      replace (woff (lden E PV) k) with (woff (lden E PV) (Z.to_nat (Z.of_nat k))) by (rewrite Nat2Z.id; reflexivity).
      apply Hvis. lia.
  - (* [comment removed for export] *)
    exists ENAMETOOLONG.
    assert (Hmp' : forall j, (j < length (firstn 4096 p))%nat ->
              in_mem (sys_input ASEGS (svc_set ms) (ms_reg ms 17)) (woff (lden E PV) j) = Some (nth j (firstn 4096 p) (Z_to_bv 8 0))).
    { intros j Hj. rewrite length_firstn in Hj. rewrite (Hmp j ltac:(lia)). rewrite app_nth1 by lia. rewrite nth_firstn.
      destruct (Nat.ltb_spec j 4096) as [_|Hc]; [reflexivity | lia]. }
    assert (Hl4 : length (firstn 4096 p) = path_max) by (rewrite length_firstn; unfold path_max; lia).
    assert (Hnz4 : Forall (fun b => b <> Z_to_bv 8 0) (firstn 4096 p)).
    { apply Forall_forall. intros b Hb. rewrite <- (firstn_skipn 4096 p) in Hnz. apply Forall_app in Hnz as [Hnz1 _].
      rewrite Forall_forall in Hnz1. exact (Hnz1 b Hb). }
    split.
    + right; right. split; [|reflexivity]. unfold read_cstr. exact (read_cstr_aux_tl _ (firstn 4096 p) (lden E PV) path_max Hl4 Hnz4 Hmp').
    + rewrite (cstr_access_len_tl _ (firstn 4096 p) (lden E PV) path_max Hl4 Hnz4 Hmp').
      apply ranges_avoid_cons; [|apply ranges_avoid_nil]. intros k Hk.
      replace (woff (lden E PV) k) with (woff (lden E PV) (Z.to_nat (Z.of_nat k))) by (rewrite Nat2Z.id; reflexivity).
      apply Hvis. unfold path_max in Hk. lia.
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hpl"] Theorem nf_handoffT : forall model0 mem0 E ms model,
  DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model ->
  INV PV PDUM [] fs0 true None mem0 E TMAIN MMAIN FSClosed model0 ->
  Forall (fact_ok (E1of E)) FSNFT ->
  HA (E1of E) MMAIN AMAIN mem0 ->
  HA3 (sarg PDUM p) (E1of E) MMAIN (snd ANFT) mem0 ->
  nf_case fs0 p ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (shp_den PDUM fs0 p (E1of E) SH_NFT).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hpl : LiaFast.U) => LiaFast.u0).
  intros model0 mem0 E ms model Hd Hi HF HAa HA Hcase.
  pose proof (den_conv_nfT model0 mem0 E ms model Hd HF) as Hd1.
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf0.
  assert (Hi1 : INV PV PDUM [] fs0 true None mem0 (E1of E) SNFT MMAIN FSClosed model0).
  { apply (INV_agree PV PDUM [] fs0 true None PD4 mem0 E (E1of E) TMAIN SNFT MMAIN MMAIN FSClosed model0 Hi); [| rewrite SNF_next, TMAIN_next; lia | reflexivity | exact Hwf0].
    rewrite TMAIN_next. exact (agree_upd NNFT E _). }
  assert (HLp : uE (E1of E) LPNFT = Z.of_nat (length p)).
  { unfold uE, LPNFT, E1of. rewrite lden_lvar. unfold upd. rewrite Pos.eqb_refl. rewrite u_small64 by (unfold two64; lia). reflexivity. }
  apply (ut_realizesM cfg Hoff Hfs PDUM fs0 p PD1 PD2 PD4 PD5 NF1T SNFT MMAIN SH_NFT ANFT _ nf1_res_eqT model0 mem0 (E1of E) ms model Hd1 Hi1
           (conj ANF_wf (conj HAa HA)) SHNF_wf).
  intros S' M' FS' sh' a' model0' mem0' E2 ms2 model2 Hin Hd2 Hi2 HX2 Hw2 Ha2.
  destruct Hin as [Heq|[]]. apply pair_inj5 in Heq. destruct Heq as (<- & <- & <- & <- & <-).
  (* [comment removed for export] *)
  apply (den_ecall ASEGS cfg LIM model0' mem0' A_wx TBLR E2 S_OPT MMAIN ms2 model2 _ TBLR_ecall S_OP_pc Hd2). intros model3 Hd3.
  destruct Hi2 as (Hpv & Hfsw & Hfr & Hm0 & Hlen & Hlk & Hfs0 & Hfds & Hc1 & Hc2 & Hdv).
  destruct HX2 as [Haw2 HA2].
  assert (HLp2 : uE E2 LPNFT = Z.of_nat (length p)).
  { rewrite <- HLp. unfold uE. rewrite (lden_agree (s_next SNFT) (E1of E) E2 LPNFT ltac:(vm_compute; reflexivity) Ha2). reflexivity. }
  destruct (nf_path model0' mem0' E2 S_OPT MMAIN ms2 model2 model3 Hd2 Hd3 (proj2 HA2) HLp2 Hcase Hfs0) as (e & Hnf & Hav).
  rewrite <- S_OP_a1 in Hnf, Hav.
  apply (den_openat_nf ASEGS cfg LIM mem0' Hfs model0' E2 S_OPT MMAIN ms2 model3 _ _ 32768 e Hd3 S_OP_a7 S_OP_a0 S_OP_a2 S_OP_fl
           ltac:(rewrite S_OP_fd; exact Hnf) Hav).
  intros ms4 m4 Hd4.
  assert (He : ERRLO <= bv_unsigned (errno_ret e) <= ERRHI).
  { destruct Hnf as [(_ & _ & _ & _ & _ & _ & _ & ->) | [(_ & ->) | (_ & ->)]]; split; apply Z.leb_le; vm_compute; reflexivity. }
  assert (Hc64 : 0 <= bv_unsigned (errno_ret e) < two64) by (unfold ERRLO, ERRHI, two64 in *; lia).
  pose proof (den_gen_ret ASEGS LIM model0' mem0' E2 S_OPT MMAIN ms4 m4 (bv_unsigned (errno_ret e)) ERRLO ERRHI Hd4 Hc64 He) as Hd5.
  set (E3 := upd E2 (s_next S_OPT) (Z_to_bv 64 (bv_unsigned (errno_ret e)))) in *.
  assert (Ha3 : agree (s_next S_OPT) E2 E3) by exact (agree_upd (s_next S_OPT) E2 _).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd2) as Hwf2.
  assert (Hle : (s_next S_OPT <= s_next TNFT)%positive) by (rewrite TNF_next; lia).
  assert (Hi3 : INV PV PDUM [] fs0 true None mem0' E3 TNFT MMAIN FSClosed model0').
  { apply (INV_agree PV PDUM [] fs0 true None PD4 mem0' E2 E3 S_OPT TNFT MMAIN MMAIN FSClosed model0'); [|exact Ha3 | exact Hle | reflexivity | exact Hwf2].
    exact (conj Hpv (conj Hfsw (conj Hfr (conj Hm0 (conj Hlen (conj Hlk (conj Hfs0 (conj Hfds (conj Hc1 (conj Hc2 Hdv)))))))))). }
  assert (HX3 : HAX awfUT (HAUT PDUM p) E3 TNFT MMAIN ANFT mem0')
    by exact (HAX_step awfUT (HAUT PDUM p) awfUT_mono (HAUT_agree PDUM p) E2 E3 S_OPT TNFT MMAIN ANFT mem0' (conj Haw2 HA2) Hwf2 Ha3 Hle).
  assert (HLp3 : uE E3 LPNFT = Z.of_nat (length p)).
  { rewrite <- HLp2. unfold uE. rewrite (lden_agree (s_next S_OPT) E2 E3 LPNFT lpnf_wf Ha3). reflexivity. }
  rewrite <- (shp_den_agree PDUM fs0 p (s_next S_OPT) E2 E3 SH_NFT ltac:(vm_compute; reflexivity) Ha3).
  assert (Hn : forall f, s_next (add_fact TNFT f) = s_next TNFT) by reflexivity.
  destruct (Z_le_gt_dec (Z.of_nat (length p)) 63) as [Hsm|Hbig].
  - apply (ut_realizesM cfg Hoff Hfs PDUM fs0 p PD1 PD2 PD4 PD5 NF2_ABT TNF_ABT MMAIN SH_NFT ANFT [] nf2_res_ab_nilT model0' mem0' E3 ms4 m4).
    + unfold TNF_ABT. apply den_addfact; [exact Hd5|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next TNFT) E3 E' LPNFT lpnf_wfT Ha').
      fold (uE E3 LPNFT). rewrite HLp3. lia.
    + exact (INV_same PV PDUM [] fs0 true None mem0' E3 TNFT TNF_ABT MMAIN FSClosed model0' Hi3 (Hn _)).
    + destruct HX3 as [Hw3 Hh3]. split; [unfold TNF_ABT; rewrite Hn; exact Hw3 | exact Hh3].
    + unfold TNF_ABT. rewrite Hn. exact SHNF_wfT.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin. destruct Hin.
  - rewrite <- SHNF2_den.
    apply (ut_realizesM cfg Hoff Hfs PDUM fs0 p PD1 PD2 PD4 PD5 KNCT TNF_CT MMAIN SH_NF2T ANFT [] nf2_res_c_nilT model0' mem0' E3 ms4 m4).
    + unfold TNF_CT. apply den_addfact; [exact Hd5|]. intros E' Ha'. cbn [fact_ok]. rewrite <- (lden_agree (s_next TNFT) E3 E' LPNFT lpnf_wfT Ha').
      fold (uE E3 LPNFT). rewrite HLp3. unfold M64, two64. lia.
    + exact (INV_same PV PDUM [] fs0 true None mem0' E3 TNFT TNF_CT MMAIN FSClosed model0' Hi3 (Hn _)).
    + destruct HX3 as [Hw3 Hh3]. split; [unfold TNF_CT; rewrite Hn; exact Hw3 | exact Hh3].
    + unfold TNF_CT. rewrite Hn. exact SHNF2_wfT.
    + intros S'' M'' FS'' sh'' a'' model0'' mem0'' E'' ms'' model'' Hin. destruct Hin.
Qed.
End NFTT.
(* [comment removed for export] *)
End AsanCoNFThmT.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanRdErrT AsanRdConvT AsanRdErrThmT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxChFamI OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanFamU OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageThmT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCoNFT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanLeafEntryT.AsanCoNFThmT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdConvT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErrThmT.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChEntM.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma HA3_transfer : forall sarg E M M' a m0 m0', sm_frz M' = sm_frz M ->
  (forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> m0' (Z_to_bv 64 w) = m0 (Z_to_bv 64 w)) ->
  sf_copies a = [] -> HA3 sarg E M a m0 -> HA3 sarg E M' a m0'.
Proof.
  intros sarg E M M' a m0 m0' Hfz Hsame Hcp [Hs Hc]. split; [|rewrite Hcp; constructor].
  rewrite Forall_forall in Hs |- *. intros r Hr. destruct (Hs r Hr) as [(C1 & C2 & C3 & C4) D].
  assert (Hw : forall w, uE E (fst (fst r)) <= w < wend (uE E (fst (fst r))) (uE E (snd (fst r))) -> m0' (Z_to_bv 64 w) = m0 (Z_to_bv 64 w)).
  { intros w Hw. destruct (proj1 (C2 w Hw)) as (p & Hp & Hpw). exact (Hsame p Hp w Hpw). }
  assert (HBw : uE E (fst (fst r)) + uE E (snd (fst r)) < wend (uE E (fst (fst r))) (uE E (snd (fst r)))).
  { unfold wend. pose proof (Z.div_mod (uE E (fst (fst r)) + uE E (snd (fst r))) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (uE E (fst (fst r)) + uE E (snd (fst r))) 8 ltac:(lia)). lia. }
  pose proof (uE_range E (fst (fst r))) as RB. pose proof (uE_range E (snd (fst r))) as RL.
  split; [split; [exact C1|split; [|split]]|].
  - intros w Hwr. destruct (C2 w Hwr) as [(p & Hp & Hpw) X2]. split; [exists p; rewrite Hfz; split; [exact Hp | exact Hpw]|].
    rewrite (Hw w Hwr). exact X2.
  - intros k Hk. rewrite (Hw (uE E (fst (fst r)) + k) ltac:(lia)). exact (C3 k Hk).
  - rewrite (Hw (uE E (fst (fst r)) + uE E (snd (fst r))) ltac:(lia)). exact C4.
  - destruct r as [[rb rl] rj]. unfold sbytes_ok in D |- *. cbn [fst snd] in *. destruct D as [E1 E2]. split; [exact E1|].
    intros i Hi. rewrite (Hw (uE E rb + i) ltac:(lia)). exact (E2 i Hi).
Qed.

Lemma MMAIN_frz : sm_frz MMAIN = sm_frz M1. Proof. vm_compute. reflexivity. Qed.
Lemma M1_frz17 : forallb (fun p => (lwf 17 (fst p) && lwf 17 (snd p))%bool) (sm_frz M1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma AMAIN_wf : awf (s_next TMAIN) AMAIN = true. Proof. vm_compute. reflexivity. Qed.
Lemma MMAIN_wfT : sm_wf (s_next TMAIN) MMAIN = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma frz_keep_agree : forall E E' (m m' : word -> option byte), agree 17 E E' ->
  (forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> m (Z_to_bv 64 w) = m' (Z_to_bv 64 w)) ->
  (forall p, In p (sm_frz M1) -> forall w, uE E' (fst p) <= w < uE E' (fst p) + uE E' (snd p) -> m (Z_to_bv 64 w) = m' (Z_to_bv 64 w)).
Proof.
  intros E E' m m' Ha H p Hp w Hw. apply (H p Hp w).
  pose proof M1_frz17 as X. rewrite forallb_forall in X. pose proof (X p Hp) as Xp. apply andb_prop in Xp as [W1 W2].
  unfold uE in *. rewrite (lden_agree 17 E E' _ W1 Ha), (lden_agree 17 E E' _ W2 Ha). exact Hw.
Qed.

Section EntryT.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.
Variables (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).
Variables (olo ohi : Z).
Hypothesis HC : olo <= OFS sp <= ohi.

#[using="Hsp Hfit Hva Hve"] Lemma pv_small : forall E, agree 17 (E0 sp brk0 draw inp) E -> uE E PV + 1 < 0x800000000000.
Proof. LiaFast.lf_pins (fun (Hsp Hfit Hva Hve : LiaFast.U) => LiaFast.u0).
  intros E Hag. pose proof (lay_nums sp draw inp Hsp Hfit Hva Hve) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  unfold uE, PV. rewrite <- (lden_agree 17 (E0 sp brk0 draw inp) E (lvar 8) ltac:(vm_compute; reflexivity) Hag). rewrite lden_lvar.
  unfold E0. change (List.nth (Pos.to_nat 8) (vals sp brk0 draw inp) (Z_to_bv 64 0)) with
    (if Nat.leb 2 (length (in_argv inp)) then cat_argv_ptr sp (in_argv inp) (in_envp inp) 1 else Z_to_bv 64 0).
  destruct (Nat.leb 2 (length (in_argv inp))) eqn:H2; [|vm_compute; reflexivity].
  apply Nat.leb_le in H2. destruct Hsp as (Hs1 & Hs2 & _).
  rewrite (u_cat_argv_ptr APH sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hva Hve Hs1 Hs2 1 ltac:(lia)).
  pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3). pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt.
  pose proof (rp_str sp draw inp Hsp Hfit Hva Hve) as Rs.
  assert (Hf1 : total_arg_bytes_nat (firstn 1 (in_argv inp)) = (length (nth 0 (in_argv inp) []) + 1)%nat).
  { destruct (in_argv inp) as [|a0 r]; [cbn in H2; lia|]. cbn [firstn nth]. rewrite firstn_O. unfold total_arg_bytes_nat. cbn [fold_right]. lia. }
  unfold cat_struct_size, auxv_size. rewrite Hf1.
  unfold usp, AC, EC, RP in *. lia.
Qed.


(* [comment removed for export] *)
#[using="Hoff Hfs Hsp Hfit Hva Hve olo ohi HC"] Theorem usage_entryT : forall mem0 E ms model,
  agree 17 (E0 sp brk0 draw inp) E ->
  DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E TMAIN MMAIN ms model ->
  HA E MMAIN AMAIN mem0 ->
  (forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) ->
  length (in_argv inp) <> 2%nat ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  intros mem0 E ms model Hag Hd HAa Hsame Hn2.
  rewrite <- (shu_spec PDUM (in_fs inp) (nth 0 (in_argv inp) []) E (uL sp brk0 draw inp Hva E Hag)).
  apply (ut_handoff cfg Hoff Hfs PDUM (in_fs inp) (nth 0 (in_argv inp) []) PD1 PD2 PD4 PD5 (model0 sp brk0 mb LIM inp) mem0 E ms model Hd).
  - apply INV_entry; [vm_compute; reflexivity|]. cbn [length PDUM]. exact (pv_small E Hag).
  - exact (usage_facts sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag Hn2).
  - exact HAa.
  - apply (HA3_transfer _ E M1 MMAIN A0 (m0 sp draw inp) mem0 MMAIN_frz Hsame eq_refl).
    exact (usage_ha3 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag PDUM).
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs Hsp Hfit Hva Hve olo ohi HC"] Theorem nf_entryT : forall mem0 E ms model,
  agree 17 (E0 sp brk0 draw inp) E ->
  DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E TMAIN MMAIN ms model ->
  HA E MMAIN AMAIN mem0 ->
  (forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) ->
  length (in_argv inp) = 2%nat -> nf_case (in_fs inp) (nth 1 (in_argv inp) []) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) (t_die (msg_cannot_open (nth 1 (in_argv inp) [])) (in_fs inp)).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  intros mem0 E ms model Hag Hd HAa Hsame H2 Hcase.
  pose proof (valid_argv_str_len (in_argv inp) 1 Hva ltac:(lia)) as Hl1.
  set (p := nth 1 (in_argv inp) []) in *.
  set (E1 := upd E NNFT (Z_to_bv 64 (Z.of_nat (length p)))).
  assert (Ha1 : agree NNFT E E1) by exact (agree_upd NNFT E _).
  assert (Ha17 : agree 17 E E1) by (apply (agree_mono 17 NNFT); [apply Pos.leb_le; vm_compute; reflexivity | exact Ha1]).
  rewrite <- (shnf_specT PDUM (in_fs inp) p E1 (uLPT sp draw inp Hsp Hfit Hva Hve E H2)).
  apply (nf_handoffT cfg Hoff Hfs (in_fs inp) p Hl1 (model0 sp brk0 mb LIM inp) mem0 E ms model Hd).
  - apply INV_entry; [vm_compute; reflexivity|]. cbn [length PDUM]. exact (pv_small E Hag).
  - exact (nf_factsT sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2).
  - exact (HA_agree NNFT E E1 MMAIN AMAIN mem0 MMAIN_wfT AMAIN_wf Ha1 HAa).
  - apply (HA3_transfer _ E1 M1 MMAIN (snd ANFT) (m0 sp draw inp) mem0 MMAIN_frz); [| reflexivity |].
    + intros q Hq w Hw. exact (frz_keep_agree E E1 mem0 (m0 sp draw inp) Ha17 (fun q Hq w Hw => Hsame q Hq w Hw) q Hq w Hw).
    + exact (nf_ha3T sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2 PDUM).
  - exact Hcase.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dirref_dot : forall p, path_is_dirref p = true -> path_eqb p dotdot_path = false -> p = [Z_to_bv 8 46].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p H1 H2. unfold path_is_dirref in H1. rewrite H2, orb_false_r in H1.
  apply path_eqb_eq in H1. rewrite H1. reflexivity.
Qed.
#[using="Hoff Hfs Hsp Hfit Hva Hve olo ohi HC"] Theorem dirref_entryT : forall mem0 E ms model,
  agree 17 (E0 sp brk0 draw inp) E ->
  DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E TMAIN MMAIN ms model ->
  HA E MMAIN AMAIN mem0 ->
  (forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) ->
  length (in_argv inp) = 2%nat -> nth 1 (in_argv inp) [] = [Z_to_bv 8 46] ->
  realizes_cfg ASEGS cfg (mkCfg ms model)
    (t_alt2 (t_die (msg_cannot_open (nth 1 (in_argv inp) [])) (in_fs inp)) (t_die (msg_read_error (nth 1 (in_argv inp) [])) (in_fs inp))).
Proof. LiaFast.lf_pins (fun (Hoff Hfs Hsp Hfit Hva Hve olo ohi HC : LiaFast.U) => LiaFast.u0).
  intros mem0 E ms model Hag Hd HAa Hsame H2 Hdot. rewrite Hdot.
  rewrite <- (shd_spec PDUM (in_fs inp) (nth 0 (in_argv inp) []) E).
  pose proof (rd_bytesT sp brk0 draw inp Hsp Hfit Hva Hve E Hag H2 Hdot) as (B1 & B2).
  pose proof (rd_p0T sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2) as HP0.
  (* [comment removed for export] *)
  assert (Hfz : forall w, uE E PV <= w < uE E PV + uE E SZR - 16 -> mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w) /\ m0 sp draw inp (Z_to_bv 64 w) <> None).
  { intros w Hw. pose proof (rd_factsT sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2 Hdot) as HF.
    rewrite Forall_forall in HF. pose proof (HF FRND ltac:(right; right; right; left; reflexivity)) as Hr. cbn [fact_ok FRND] in Hr.
    fold (uE E SZR) in Hr.
    assert (HSZ : uE E SZR = uE E RANDP16 - uE E PV).
    { pose proof (HF FV8 ltac:(right; left; reflexivity)) as Hv. cbn [fact_ok FV8] in Hv. fold (uE E PV) in Hv.
      unfold SZR in Hr |- *. fold (uE E (lsub RANDP16 PV)) in Hr |- *.
      destruct (small_diff E RANDP16 PV 18 2400000 Hr) as [[Hl He]|[Hl He]]; [lia|].
      pose proof (uE_range E RANDP16). unfold two64 in *. lia. }
    assert (Hq : RANDP16 = laddc RANDP 16) by (vm_compute; reflexivity).
    assert (HR : uE E RANDP16 = uE E RANDP + 16).
    { rewrite Hq. apply uE_laddc; [lia|]. pose proof (uE_range E RANDP16) as X. rewrite Hq in X. pose proof (uE_range E RANDP) as Y.
      rewrite (uRANDP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag). pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & _).
      pose proof (usp_b sp inp Hsp Hfit Hva Hve) as (U1 & U2). pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt. unfold usp, two64 in *. lia. }
    pose proof (uP0 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag) as EP0.
    pose proof (uRANDP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag) as ERP.
    pose proof (rp_b sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3).
    change (fst FRZT) with P0 in HP0. rewrite EP0 in HP0. rewrite ERP in HR.
    pose proof (uE_range E RANDP) as YR. rewrite ERP in YR. pose proof (uE_range E PV) as YP.
    split.
    - apply (Hsame (P0, lsub RANDP P0)); [rewrite M1_frz; right; left; reflexivity|]. cbn [fst snd].
      rewrite uE_lsub_small by (rewrite ERP, EP0; unfold usp, AC, EC in *; lia).
      rewrite EP0, ERP. lia.
    - destruct (m0_in sp draw inp (Z_to_bv 64 w)) as (b & Hb & _); [|rewrite Hb; discriminate].
      rewrite u_small64 by (unfold two64 in *; lia).
      unfold usp, AC, EC in *. lia. }
  apply (rd_handoffT cfg Hoff Hfs [Z_to_bv 8 46] (in_fs inp) (nth 0 (in_argv inp) []) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(cbn; unfold path_max; lia) ltac:(constructor; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate | constructor])
           (model0 sp brk0 mb LIM inp) mem0 E ms model Hd).
  - apply INV_entry; [vm_compute; reflexivity|]. cbn [length]. pose proof (pv_small E Hag). lia.
  - exact HAa.
  - exact (rd_factsT sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2 Hdot).
  - exact HP0.
  - intros w Hw. destruct (Hfz w Hw) as [X Y]. rewrite X. exact Y.
  - destruct (Hfz (uE E PV) ltac:(pose proof (rd_factsT sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2 Hdot) as HF; rewrite Forall_forall in HF;
                                 pose proof (HF FRND ltac:(right; right; right; left; reflexivity)) as Hr; cbn [fact_ok FRND] in Hr; fold (uE E SZR) in Hr; lia)) as [X1 _].
    destruct (Hfz (uE E PV + 1) ltac:(pose proof (rd_factsT sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC E Hag H2 Hdot) as HF; rewrite Forall_forall in HF;
                                 pose proof (HF FRND ltac:(right; right; right; left; reflexivity)) as Hr; cbn [fact_ok FRND] in Hr; fold (uE E SZR) in Hr; lia)) as [X2 _].
    rewrite X1, X2. exact (conj B1 B2).
Qed.
End EntryT.
(* [comment removed for export] *)
