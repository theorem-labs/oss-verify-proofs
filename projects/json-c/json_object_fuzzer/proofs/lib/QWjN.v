(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_pe.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaBw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaBw.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := tt.
End GwI.

Section M.
Variables (txt : list Z) (p : Z).
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.

Local Notation JF := (JF txt p).
Local Notation JR := (JR p).

#[using="BYT Hp Hnul"] Lemma JF_getc' : forall k c f c2 f2, JF k c f -> c <> 0 -> sh_getc f = (c2, f2) -> JF (k + 1) c2 f2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_getc') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_getc')]. Qed.

#[using="Type"] Lemma JF_JR : forall k c f, JF k c f -> c <> 0 -> JR f.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_JR)]. Qed.
#[using="Hp"] Lemma JF_unget_JR : forall k c f, JF k c f -> 1 <= k -> JF (k - 1) 0 (sh_unget f) /\ JR (sh_unget f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_unget_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_unget_JR)]. Qed.
#[using="Hp"] Lemma JF_ungets_JR : forall n k c f, JF k c f -> Z.of_nat n <= k -> (1 <= n)%nat -> JR (fs_unget_loop n f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_ungets_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JF_ungets_JR)]. Qed.
#[using="Type"] Lemma JR_lim0' : forall f, JR f -> JR (sh_lim0 f).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JR_lim0') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.JR_lim0')]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QzgB.JR) (@QaBw.JR) (Q6nq.gwt_def (@QzgB.JF) (@QaBw.JF) Q6nq.gwt_nil)).
#[using="BYT Hp Hnul"] Lemma fs_ws_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_ws_J)]. Qed.

#[using="Type"] Lemma lor32_nz : forall c v, (Z.lor c 32 =? v) = true -> 97 <= v -> c <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.lor32_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.lor32_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_inf_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_inf_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_nan_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_nan_J)]. Qed.

#[using="Type"] Lemma alnum_nz : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz) [] '([(-97); (-65); 95]%Z : list Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.alnum_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma fs_par_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.fs_par_J)]. Qed.

#[using="BYT Hp Hnul"] Lemma df_lz_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_Jk)]. Qed.
#[using="BYT Hp Hnul"] Lemma df_rz_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_Jk)]. Qed.

#[using="Type"] Lemma ishexc_nz : forall c, ishexc c = true -> c <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.ishexc_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.ishexc_nz)]. Qed.
#[using="Type"] Lemma hx_dig_cond_nz : forall s, hx_dig_cond s = true -> hx_c s <> 0.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_cond_nz) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_cond_nz)]. Qed.

#[using="BYT Hp Hnul"] Lemma hx_dig_Jk : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hx_dig_Jk)]. Qed.

#[using="Type"] Lemma df_lz_0 : forall n g f r, df_lz_loop n (g, 0, f) = Some r -> r = (g, 0, f).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_lz_0)]. Qed.
#[using="Type"] Lemma df_rz_0 : forall n g l f r, df_rz_loop n (g, l, 0, f) = Some r -> r = (g, l, 0, f).
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.df_rz_0)]. Qed.

Section HXJ.
Variables (fuelc : nat) (bits emin sign pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation HX_e2' := (HX_e2 bits emin sign).
Local Notation HX_rz' := (HX_rz fuelc bits emin sign pok).
Local Notation HX_alz' := (HX_alz fuelc bits emin sign pok).
Local Notation HX_lz' := (HX_lz fuelc bits emin sign pok).

#[using="Type"] Lemma HX_e2_f : forall f x y e2 f' y', HX_e2' f x y e2 = Some (f', y') -> f' = f.
Proof. first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_e2_f) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_e2_f)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_tail_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_tail_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_dig_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_dig_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_rz_J : forall gd rp c f k f' y', HX_rz' gd rp c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_rz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_rz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_alz_J : forall gd c f k f' y', HX_alz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_alz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_alz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_lz_J : forall gd c f k f' y', HX_lz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_lz_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.HX_lz_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma hexfloat_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.hexfloat_J)]. Qed.
End HXJ.

Section FSJ.
Variables (fuelc : nat) (pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation FS_zero' := (FS_zero fuelc 53 (-1074) pok).
Local Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Local Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

#[using="BYT Hp Hnul Hpk"] Lemma FS_zero_J : forall sg c2 f2 k f' y', FS_zero' sg c2 f2 = Some (f', y') -> JF k c2 f2 -> 2 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_zero_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_zero_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_tail_h_J : forall sg c f k f' y', FS_tail_h' sg c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_tail_h_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_tail_h_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_nan_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_nan_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_inf_J : ltac2:(Q6nq.ty1 'GwI.segs '(@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J) [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_inf_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_sign_J : forall c f k f' y', FS_sign' c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_sign_J) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.FS_sign_J)]. Qed.

#[using="BYT Hp Hnul Hpk"] Lemma floatscan_h_JR : forall f f' y, floatscan_h fuelc f 1 pok = Some (f', y) -> JF 0 1 f -> JR f'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_JF__3; @gw_eq_JF__2; @gw_eq_JF]; [@gw_eq_JR__3; @gw_eq_JR__2; @gw_eq_JR]]); first [GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.floatscan_h_JR) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.F_rscan_modelH.floatscan_h_JR)]. Qed.
End FSJ.
End M.
