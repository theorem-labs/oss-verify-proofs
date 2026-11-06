(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChNull FxChFix FxChAdd FxChFixNew FxChain FxChSep FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg AcEntry AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand AcUnwApp AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps.AcP0gen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition F5000 : nat := 5000.
Definition F30000 : nat := 30000.
Definition single (o : option (list sst)) : option sst := match o with Some [L] => Some L | _ => None end.
Definition ASEGSR : list (word * word) := segments_reserved Asan.M.loaded_segments.
Definition uch1_ok0 (L : sst) (spl : lin) (lo : Z) : bool :=
  match nth_error (s_rgs L) 8 with
  | Some (RG b z RW c) =>
      (lin_eqb b (laddc spl (-56)) && lin_eqb z (lconst 56) &&
       match tget (Pos.of_succ_nat 40) c with Some (BK b0) => (Z.leb 0 b0 && Z.ltb b0 256 && Z.leb b0 lo)%bool | _ => false end &&
       forallb (fun j => match tget (Pos.of_succ_nat (40 + j)) c with Some (BK 0) => true | _ => false end) (seq 1 7))%bool
  | _ => false
  end.
Lemma uch1_ok0_sound : forall L spl lo, uch1_ok0 L spl lo = true ->
  exists c b0, nth_error (s_rgs L) 8 = Some (RG (laddc spl (-56)) (lconst 56) RW c) /\ tget (Pos.of_succ_nat 40) c = Some (BK b0) /\ 0 <= b0 < 256 /\ b0 <= lo /\ (forall j, (1 <= j < 8)%nat -> tget (Pos.of_succ_nat (40 + j)) c = Some (BK 0)).
Proof.
  intros L spl lo H. unfold uch1_ok0 in H. destruct (nth_error (s_rgs L) 8) as [[b z k c]|] eqn:H8; [|discriminate].
  destruct k; try discriminate.
  apply andb_prop in H as [H Hj]. apply andb_prop in H as [H Hb0]. apply andb_prop in H as [Hb Hz]. apply lin_eqb_eq in Hb, Hz. subst b z.
  destruct (tget (Pos.of_succ_nat 40) c) as [[b0|l0 j0]|] eqn:H40; try discriminate.
  apply andb_prop in Hb0 as [Hb0 Hle]. apply andb_prop in Hb0 as [Hlo Hhi]. apply Z.leb_le in Hlo, Hle. apply Z.ltb_lt in Hhi.
  exists c, b0. split; [first [exact H8 | reflexivity]|]. split; [first [exact H40 | reflexivity]|]. split; [lia|]. split; [exact Hle|].
  intros j Hj'. rewrite forallb_forall in Hj. specialize (Hj j ltac:(apply in_seq; lia)).
  destruct (tget (Pos.of_succ_nat (40 + j)) c) as [[bj|l1 j1]|]; try discriminate. destruct bj as [|p|p]; try discriminate. reflexivity.
Qed.
Fixpoint find_grant_acc (gs : list (lin * lin * gkind)) (b : lin) (z : Z) (i : nat) : option nat :=
  match gs with [] => None | g :: l' => if (lin_eqb (fst (fst g)) b && lin_eqb (snd (fst g)) (lconst z))%bool then Some i else find_grant_acc l' b z (Datatypes.S i) end.
Definition find_grant (gs : list (lin * lin * gkind)) (b : lin) (z : Z) : option nat := find_grant_acc gs b z O.
Lemma find_grant_acc_sound : forall gs b z i j, find_grant_acc gs b z i = Some j -> (i <= j)%nat /\ exists k, nth_error gs (j - i) = Some (b, lconst z, k).
Proof.
  induction gs as [|g l IH]; intros b z i j H; cbn [find_grant_acc] in H; [discriminate|].
  destruct (lin_eqb (fst (fst g)) b && lin_eqb (snd (fst g)) (lconst z))%bool eqn:Hg.
  - injection H as <-. apply andb_prop in Hg as [H1 H2]. apply lin_eqb_eq in H1, H2.
    split; [lia|]. exists (snd g). rewrite Nat.sub_diag. cbn. destruct g as [[b' z'] k']. cbn in *. subst. reflexivity.
  - destruct (IH b z (Datatypes.S i) j H) as [Hle (k & Hk)]. split; [lia|]. exists k.
    replace (j - i)%nat with (Datatypes.S (j - Datatypes.S i)) by lia. exact Hk.
Qed.
Lemma find_grant_sound : forall gs b z j, find_grant gs b z = Some j -> exists k, nth_error gs j = Some (b, lconst z, k).
Proof. intros gs b z j H. destruct (find_grant_acc_sound gs b z O j H) as [_ (k & Hk)]. exists k. rewrite Nat.sub_0_r in Hk. exact Hk. Qed.
(* [comment removed for export] *)
Lemma find_grant_nomark : forall gs b z j, find_grant gs b z = Some j -> forall k, is_mark (b, lconst z, k) = false.
Proof. intros gs b z j _ k. apply is_mark_csize. Qed.
(* [comment removed for export] *)
Definition hint_sh (R : region) : bool := Z.leb SH_LO (l_c (rg_base R)) &&& Z.ltb (l_c (rg_base R)) SH_HI.
Definition dep_sep_f3 (fs : list fact) (gs : list (lin * lin * gkind)) (res : list (word * word)) (jD1 jB1 : nat) (sp D1l B1l : lin)
    (nsD nsB : bool) (xi : unit -> bool) (R : region) : bool :=
  (* [comment removed for export] *)
  match is_const (rg_base R), is_const (rg_size R) with
  | Some _, Some _ => if dep_sep_f fs gs res jD1 jB1 sp D1l B1l R then true else xi tt
  | _, _ => if band_few fs sp R then true
            else if (hint_sh R &&& nsD &&& nsB &&& sep_shadow_b fs R) then true
            else if cont_bm true fs gs jD1 jB1 R then true    (* [comment removed for export] *)
            else if grant_in_e fs gs jD1 jB1 R then true      (* [comment removed for export] *)
            else if cont_bm false fs gs jD1 jB1 R then true
            else if xi tt then true
            else if (negb (hint_sh R) &&& nsD &&& nsB &&& sep_shadow_b fs R) then true
            else dep_sep_f fs gs res jD1 jB1 sp D1l B1l R
  end.
Lemma dep_sep_f3_spec : forall fs gs res jD1 jB1 sp D1l B1l nsD nsB xi R,
  nsD = sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) -> nsB = sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) ->
  dep_sep_f3 fs gs res jD1 jB1 sp D1l B1l nsD nsB xi R = true ->
  xi tt = true \/ dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true \/ grant_in_e fs gs jD1 jB1 R = true.
Proof.
  intros fs gs res jD1 jB1 sp D1l B1l nsD nsB xi R -> -> H. unfold dep_sep_f3 in H.
  assert (Ksh : (is_const (rg_base R) = None \/ is_const (rg_size R) = None) -> forall h : bool,
              (h &&& sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) = true ->
              dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true).
  { intros Hn h Hh. destruct h; [|discriminate]. destruct (sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty)) eqn:N1; [|discriminate].
    destruct (sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty)) eqn:N2; [|discriminate].
    destruct (sep_shadow_b fs R) eqn:Hs; [|discriminate]. exact (dep_sep_b_shadow fs gs res jD1 jB1 sp D1l B1l R N1 N2 Hs Hn). }
  assert (K : (is_const (rg_base R) = None \/ is_const (rg_size R) = None) ->
              (if band_few fs sp R then true
               else if (hint_sh R &&& sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) then true
               else if cont_bm true fs gs jD1 jB1 R then true
               else if grant_in_e fs gs jD1 jB1 R then true
               else if cont_bm false fs gs jD1 jB1 R then true
               else if xi tt then true
               else if (negb (hint_sh R) &&& sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) then true
               else dep_sep_f fs gs res jD1 jB1 sp D1l B1l R) = true ->
              xi tt = true \/ dep_sep_b fs gs res jD1 jB1 sp D1l B1l R = true \/ grant_in_e fs gs jD1 jB1 R = true).
  { intros Hn H0.
    destruct (band_few fs sp R) eqn:Hbf.
    { right. left. unfold band_few in Hbf. destruct (few_t (lsub sp (rg_base R))); [|discriminate]. exact (dep_sep_b_band fs gs res jD1 jB1 sp D1l B1l R Hbf Hn). }
    destruct (hint_sh R &&& sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) eqn:H1.
    { right. left. exact (Ksh Hn _ H1). }
    destruct (cont_bm true fs gs jD1 jB1 R) eqn:Hc0.
    { right. left. destruct (cont_bm_sep true fs gs jD1 jB1 R Hc0) as [A B]. exact (dep_sep_b_grant fs gs res jD1 jB1 sp D1l B1l R A B Hn). }
    destruct (grant_in_e fs gs jD1 jB1 R) eqn:Hg; [right; right; reflexivity|].
    destruct (cont_bm false fs gs jD1 jB1 R) eqn:Hc.
    { right. left. destruct (cont_bm_sep false fs gs jD1 jB1 R Hc) as [A B]. exact (dep_sep_b_grant fs gs res jD1 jB1 sp D1l B1l R A B Hn). }
    destruct (xi tt); [left; reflexivity|].
    destruct (negb (hint_sh R) &&& sep_noshadow_b fs (RGz D1l 1048576 RZ TEmpty) &&& sep_noshadow_b fs (RGz B1l 8388608 RZ TEmpty) &&& sep_shadow_b fs R) eqn:H2.
    { right. left. exact (Ksh Hn _ H2). }
    right. left. rewrite dep_sep_f_eq in H0; exact H0. }
  destruct (is_const (rg_base R)) as [cb|] eqn:Eb; [destruct (is_const (rg_size R)) as [cz|] eqn:Ez|].
  - destruct (dep_sep_f fs gs res jD1 jB1 sp D1l B1l R) eqn:Hf; [right; left; rewrite dep_sep_f_eq in Hf; exact Hf | left; exact H].
  - apply K; [right; reflexivity | exact H].
  - apply K; [left; reflexivity | exact H].
Qed.
Definition dep_ok (M : smodel) (a : ast) (T : sst) : bool :=
  match find_grant (sm_maps M) (fst (a_dep a)) 1048576, find_grant (sm_maps M) (snd (a_dep a)) 8388608 with
  | Some jD1, Some jB1 =>
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      let nsD := sep_noshadow_b (s_facts T) (RGz (fst (a_dep a)) 1048576 RZ TEmpty) in
      let nsB := sep_noshadow_b (s_facts T) (RGz (snd (a_dep a)) 8388608 RZ TEmpty) in
      (* [comment removed for export] *)
      let pc := match a_pri a with [] => false | _ => true end in
      forallb (fun R => if (if pc then sep_cached a R else false) then true
                        else dep_sep_f3 (s_facts T) (sm_maps M) ASEGSR jD1 jB1 (sm_sp M) (fst (a_dep a)) (snd (a_dep a)) nsD nsB
                               (fun _ => if (match a_pri a with [] => false | _ => ext_in (s_facts T) a R end) then true
                                         (* [comment removed for export] *)
                                         else (nsD &&& nsB &&& grant_in_sh (s_facts T) (sm_maps M) jD1 R)) R) (s_rgs T)
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition band_ok (fs : list fact) (M : smodel) (spl : lin) : bool :=
  match lin_off spl (sm_sp M) with
  | Some d => (Z.leb (two64 - 8388608 + 8192) d && Z.ltb d two64)%bool
  | None => (* [comment removed for export] *)
            (Z.leb 1 (fst (irange fs (lsub (sm_sp M) spl))) && Z.leb (snd (irange fs (lsub (sm_sp M) spl))) (8388608 - 8192))%bool
  end.
(* [comment removed for export] *)
Definition obind {A B} (o : option A) (f : A -> option B) : option B := match o with Some x => f x | None => None end.
Definition obool {B} (b : bool) (x : option B) : option B := if b then x else None.
Lemma obind_some : forall {A B} (o : option A) (f : A -> option B) r, obind o f = Some r -> exists x, o = Some x /\ f x = Some r.
Proof. intros A B [x|] f r H; cbn in H; [exists x; split; [reflexivity | exact H] | discriminate]. Qed.
Lemma obool_some : forall {B} b (x : option B) r, obool b x = Some r -> b = true /\ x = Some r.
Proof. intros B [|] x r H; cbn in H; [split; [reflexivity | exact H] | discriminate]. Qed.

Lemma agree_trans' : forall n E1 E2 E3, agree n E1 E2 -> agree n E2 E3 -> agree n E1 E3.
Proof. intros n E1 E2 E3 H1 H2 x Hx. rewrite (H1 x Hx). exact (H2 x Hx). Qed.
Lemma agree_le' : forall n n' E1 E2, (n <= n')%positive -> agree n' E1 E2 -> agree n E1 E2.
Proof. intros n n' E1 E2 Hle H x Hx. apply H. lia. Qed.

Lemma terms_eqb_refl' : forall x, terms_eqb x x = true.
Proof. induction x as [|[p k] x IH]; [reflexivity|]. cbn. rewrite Pos.eqb_refl, Z.eqb_refl, IH. reflexivity. Qed.
Lemma lin_eqb_neq : forall a b, lin_eqb a b = false -> a <> b.
Proof. intros a b H ->. unfold lin_eqb in H. rewrite Z.eqb_refl, terms_eqb_refl' in H. discriminate. Qed.

Section MALlib.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Type"] Lemma single_some : forall o L, single o = Some L -> o = Some [L].
Proof. LiaFast.lf_pins LiaFast.u0. intros [[|x [|y l]]|] L H; cbn in H; try discriminate. injection H as <-. reflexivity. Qed.
#[using="Type"] Lemma In_single : forall {A} (x y : A), In x [y] -> x = y.
Proof. LiaFast.lf_pins LiaFast.u0. intros A x y [H|[]]. symmetry. exact H. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma band_hi : forall mem0 E L M ms model spl g, DEN ASEGS LIMIT model0 mem0 E L M ms model -> band_ok (s_facts L) M spl = true ->
  In g (sm_maps M) -> uE E (fst (fst g)) + gsz E g + 4320 <= bv_unsigned (lden E spl).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E L M ms model spl g Hd Hb Hg.
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt. specialize (Hgt g Hg).
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as Hsp. destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hok Hhi].
  pose proof (alloc_top_lo _ Hok) as Hlo. unfold alloc_top in Hgt, Hlo. rewrite Hsp in Hgt, Hlo, Hhi.
  unfold band_ok in Hb. destruct (lin_off spl (sm_sp M)) as [d|] eqn:Hd'.
  2:{ (* [comment removed for export] *)
      apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      assert (HF : Forall (fact_ok E) (s_facts L)) by (destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
      pose proof (irange_sound E (s_facts L) (lsub (sm_sp M) spl) HF) as Hs.
      rewrite lden_lsub, bv_sub_unsigned in Hs. unfold bv_wrap, bv_modulus in Hs. change (2 ^ Z.of_N 64) with two64 in Hs.
      pose proof (bv_unsigned_in_range _ (lden E spl)) as Rs. pose proof (bv_unsigned_in_range _ (lden E (sm_sp M))) as Ri.
      unfold bv_modulus in Rs, Ri. change (2 ^ Z.of_N 64) with two64 in Rs, Ri.
      unfold stack_max_size, sp_window_hi, two64 in *.
      destruct (Z_le_gt_dec (bv_unsigned (lden E spl)) (bv_unsigned (lden E (sm_sp M)))) as [Hle|Hgt'].
      - rewrite Z.mod_small in Hs by lia. lia.
      - assert (Q : (bv_unsigned (lden E (sm_sp M)) - bv_unsigned (lden E spl)) mod 18446744073709551616
                    = bv_unsigned (lden E (sm_sp M)) - bv_unsigned (lden E spl) + 18446744073709551616)
          by (symmetry; apply Z.mod_unique with (-1); [left; lia | lia]).
        rewrite Q in Hs. lia. }
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (lin_off_sound E spl (sm_sp M) d Hd') as [Hl Hr]. rewrite lden_lsub in Hl.
  assert (X : bv_unsigned (lden E spl) = (bv_unsigned (lden E (sm_sp M)) + d) mod two64).
  { assert (Y : lden E spl = (Z_to_bv 64 d + lden E (sm_sp M))%bv) by (rewrite <- Hl; apply bv_eq; rewrite bv_add_unsigned, bv_sub_unsigned;
      unfold bv_wrap, bv_modulus; rewrite Zplus_mod_idemp_l; replace (bv_unsigned (lden E spl) - bv_unsigned (lden E (sm_sp M)) + bv_unsigned (lden E (sm_sp M))) with (bv_unsigned (lden E spl)) by lia;
      symmetry; apply Z.mod_small; apply bv_unsigned_in_range).
    rewrite Y, bv_add_unsigned, u_small64 by exact Hr. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. f_equal. lia. }
  rewrite X. unfold stack_max_size, sp_window_hi, two64 in *.
  assert (Q : (bv_unsigned (lden E (sm_sp M)) + d) mod 18446744073709551616 = bv_unsigned (lden E (sm_sp M)) + d - 18446744073709551616).
  { symmetry. apply Z.mod_unique with 1; [left; lia | lia]. }
  rewrite Q. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma grant_sh_not_downed : forall mem0 E L M ms model D1l B1l jD1 R, DEN ASEGS LIMIT model0 mem0 E L M ms model ->
  sep_noshadow_b (s_facts L) (RGz D1l 1048576 RZ TEmpty) = true -> sep_noshadow_b (s_facts L) (RGz B1l 8388608 RZ TEmpty) = true ->
  grant_in_sh (s_facts L) (sm_maps M) jD1 R = true ->
  forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> ~ downed (uE E D1l) (uE E B1l) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E L M ms model D1l B1l jD1 R Hd N1 N2 Hgs x Hw Hdw.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as Hd0. destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
  destruct (grant_in_sh_pts E (s_facts L) (sm_maps M) HF (dn_gsh _ _ _ _ _ _ _ _ _ Hd) jD1 R Hgs x Hw) as (Hso & i & g & _ & Hn & _ & Hwg).
  pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt. specialize (Hgt g (nth_error_In _ _ Hn)).
  destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [_ Hshi]. unfold alloc_top, stack_max_size in Hgt. unfold sp_window_hi in Hshi.
  assert (Hsh : in_shadow x = true).
  { unfold in_shadow. apply andb_true_intro. unfold SH_LO, SH_HI, SH_OFF in *. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]].
  - unfold DT_LO, DT_HI, SH_OFF in *. lia.
  - unfold DF_LO, DF_HI, SH_OFF in *. lia.
  - assert (Hin : uE E (rg_base (RGz D1l 1048576 RZ TEmpty)) <= x < uE E (rg_base (RGz D1l 1048576 RZ TEmpty)) + rsz E (RGz D1l 1048576 RZ TEmpty)).
    { unfold RGz, rsz. cbn [rg_base rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). exact D. }
    rewrite (noshadow_sound E (s_facts L) _ HF N1 x Hin) in Hsh. discriminate.
  - assert (Hin : uE E (rg_base (RGz B1l 8388608 RZ TEmpty)) <= x < uE E (rg_base (RGz B1l 8388608 RZ TEmpty)) + rsz E (RGz B1l 8388608 RZ TEmpty)).
    { unfold RGz, rsz. cbn [rg_base rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). exact D. }
    rewrite (noshadow_sound E (s_facts L) _ HF N2 x Hin) in Hsh. discriminate.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dep_outside_den : forall mem0 E L M ms model a m0, DEN ASEGS LIMIT model0 mem0 E L M ms model -> HA_on E M a m0 -> dep_ok M a L = true ->
  forall x, 0 <= x < two64 -> downed (uE E (fst (a_dep a))) (uE E (snd (a_dep a))) x -> outside E (s_rgs L) (Z_to_bv 64 x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E L M ms model a m0 Hd HA0 Hok x Hx Hdw. unfold dep_ok in Hok. cbv zeta in Hok.
  destruct (find_grant (sm_maps M) (fst (a_dep a)) 1048576) as [jD1|] eqn:HD1; [|discriminate].
  destruct (find_grant (sm_maps M) (snd (a_dep a)) 8388608) as [jB1|] eqn:HB1; [|discriminate].
  destruct (find_grant_sound _ _ _ _ HD1) as (kD & HgD). destruct (find_grant_sound _ _ _ _ HB1) as (kB & HgB).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as Hd0.
  destruct Hd0 as (_ & _ & _ & _ & Hrgs & _ & HF & _).
  destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hsok Hshi].
  unfold outside. apply Forall_forall. intros R HR. rewrite forallb_forall in Hok. specialize (Hok R HR).
  rewrite Forall_forall in Hrgs. destruct (Hrgs R HR) as (P1 & P2 & _).
  destruct (if match a_pri a with [] => false | _ => true end then sep_cached a R else false) eqn:Hch.
  { (* [comment removed for export] *)
    assert (Hne : a_pri a <> []) by (destruct (a_pri a); [discriminate Hch | discriminate]).
    assert (Hsc : sep_cached a R = true) by (destruct (a_pri a); [discriminate Hch | exact Hch]).
    pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
    rewrite u_small64 by exact Hx.
    destruct (Z_lt_le_dec x (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) x) as [Y|Y]; [right; exact Y|]. exfalso.
    refine (sep_cached_gen E a (downed (dD1 E a) (dB1 E a)) R _ P1 P2 Hsc x _ Hdw).
    - intros p Hp. split; [exact (proj1 (po_sep _ _ _ _ HP0 p Hp)) | exact (po_sepd _ _ _ _ HP0 p Hp)].
    - unfold uE. lia. }
  destruct (dep_sep_f3_spec _ _ _ _ _ _ _ _ _ _ _ R eq_refl eq_refl Hok) as [Hxa|Hrest]; cbv beta in *.
  - destruct (match a_pri a with [] => false | _ => ext_in (s_facts L) a R end) eqn:Hxe.
    2:{ (* [comment removed for export] *)
      destruct (sep_noshadow_b (s_facts L) (RGz (fst (a_dep a)) 1048576 RZ TEmpty)) eqn:N1; [|cbv beta iota in Hxa; discriminate Hxa].
      destruct (sep_noshadow_b (s_facts L) (RGz (snd (a_dep a)) 8388608 RZ TEmpty)) eqn:N2; [|cbv beta iota in Hxa; discriminate Hxa].
      cbv beta iota in Hxa.
      rewrite u_small64 by exact Hx.
      destruct (Z_lt_le_dec x (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) x) as [Y|Y]; [right; exact Y|]. exfalso.
      assert (Hw : uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R) by (unfold uE; lia).
      exact (grant_sh_not_downed mem0 E L M ms model _ _ jD1 R Hd N1 N2 Hxa x Hw Hdw). }
    clear Hxa. rename Hxe into Hxa.
    (* [comment removed for export] *)
    assert (Hne : a_pri a <> []) by (destruct (a_pri a); [discriminate Hxa | discriminate]).
    assert (Hxi : ext_in (s_facts L) a R = true) by (destruct (a_pri a); [discriminate Hxa | exact Hxa]).
    destruct (ha_pri _ _ _ _ HA0 Hne) as [Hi _ _ _ _ _ Hxt _].
    destruct (ext_in_sound E (s_facts L) HF a m0 Hi Hxt R P1 Hxi) as (c & Hc & Hl).
    rewrite u_small64 by exact Hx.
    destruct (Z_lt_le_dec x (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) x) as [Y|Y]; [right; exact Y|]. exfalso.
    apply (pri_not_downed LIMIT model0 mem0 E L M ms model a m0 Hd HA0 Hne x); [|exact Hdw].
    unfold pri_foot, pri_foot_z. right. right. right. exists c. split; [exact Hc|].
    pose proof Hi as Hi0. unfold INV_A in Hi0. destruct Hi0 as [_ _ _ _ _ _ _ _ _ _ _ Hcls].
    unfold uE in Hl. destruct Hl as [(L1 & L2 & L3)|(L1 & L2 & L3)].
    + left. destruct (Hcls c Hc) as [(J0 & _)|(J1 & Z1 & _)]; [rewrite J0 in L2; lia|]. rewrite Z1. lia.
    + right. right. left. lia.
  - destruct Hrest as [Hokb|Hgi].
    2:{ (* [comment removed for export] *)
      rewrite u_small64 by exact Hx.
      destruct (Z_lt_le_dec x (bv_unsigned (lden E (rg_base R)))) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) x) as [Y|Y]; [right; exact Y|]. exfalso.
      assert (Hw : uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R) by (unfold uE; lia).
      destruct (grant_in_pts E (s_facts L) (sm_maps M) model _ HF (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
                  (dn_gsh _ _ _ _ _ _ _ _ _ Hd) jD1 jB1 R Hgi x Hw) as (Hcov & _ & Hdj).
      destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]].
      - pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hcov) as Hnr. rewrite (res_pts model (dn_res _ _ _ _ _ _ _ _ _ Hd) x (or_introl D)) in Hnr. discriminate.
      - pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hcov) as Hnr. rewrite (res_pts model (dn_res _ _ _ _ _ _ _ _ _ Hd) x (or_intror D)) in Hnr. discriminate.
      - apply (Hdj jD1 _ HgD (find_grant_nomark _ _ _ _ HD1 _) (or_introl eq_refl)). cbn [fst snd]. unfold gsz. cbn [fst snd].
        replace (uE E (lconst 1048576)) with 1048576 by (unfold uE; rewrite lden_lconst; symmetry; apply u_small64; unfold two64; lia). exact D.
      - apply (Hdj jB1 _ HgB (find_grant_nomark _ _ _ _ HB1 _) (or_intror eq_refl)). cbn [fst snd]. unfold gsz. cbn [fst snd].
        replace (uE E (lconst 8388608)) with 8388608 by (unfold uE; rewrite lden_lconst; symmetry; apply u_small64; unfold two64; lia). exact D. }
    assert (Hbnd : Forall (fun R0 => 0 <= rsz E R0 /\ uE E (rg_base R0) + rsz E R0 <= two64) [R]) by (constructor; [split; [exact P1 | exact P2] | constructor]).
    assert (Hok1 : forallb (dep_sep_b (s_facts L) (sm_maps M) (vm_reserved (m_vmmaps model)) jD1 jB1 (sm_sp M) (fst (a_dep a)) (snd (a_dep a))) [R] = true).
    { cbn [forallb]. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd). fold ASEGSR. rewrite Hokb. reflexivity. }
    pose proof (dep_outside_rgs E (s_facts L) (sm_maps M) model (sm_sp M) _ HF (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
           (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) Hshi Hsok (dn_mres _ _ _ _ _ _ _ _ _ Hd)
           (dn_res _ _ _ _ _ _ _ _ _ Hd) [R] jD1 jB1 _ _ (fst (a_dep a)) (snd (a_dep a)) Hbnd HgD eq_refl eq_refl HgB eq_refl eq_refl (find_grant_nomark _ _ _ _ HD1 _) (find_grant_nomark _ _ _ _ HB1 _) Hok1 x Hx Hdw) as Ho.
    unfold outside in Ho. exact (Forall_inv Ho).
Qed.
(* [comment removed for export] *)
Definition dep_cacheable (fs : list fact) (M : smodel) (a : ast) (jD1 jB1 : nat) (nsD nsB : bool) (R : region) : bool :=
  dep_sep_f3 fs (sm_maps M) ASEGSR jD1 jB1 (sm_sp M) (fst (a_dep a)) (snd (a_dep a)) nsD nsB (fun _ => false) R.
#[using="Type"] Lemma dep_cacheable_pts : forall mem0 E L M ms model a m0 jD1 jB1 R, DEN ASEGS LIMIT model0 mem0 E L M ms model -> HA_on E M a m0 ->
  find_grant (sm_maps M) (fst (a_dep a)) 1048576 = Some jD1 -> find_grant (sm_maps M) (snd (a_dep a)) 8388608 = Some jB1 ->
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  dep_cacheable (s_facts L) M a jD1 jB1 (sep_noshadow_b (s_facts L) (RGz (fst (a_dep a)) 1048576 RZ TEmpty))
    (sep_noshadow_b (s_facts L) (RGz (snd (a_dep a)) 8388608 RZ TEmpty)) R = true ->
  forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> ~ downed (dD1 E a) (dB1 E a) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E L M ms model a m0 jD1 jB1 R Hd HA0 HD1 HB1 P1 P2 Hok x Hw Hdw. unfold dep_cacheable in Hok. unfold dD1, dB1 in Hdw.
  destruct (find_grant_sound _ _ _ _ HD1) as (kD & HgD). destruct (find_grant_sound _ _ _ _ HB1) as (kB & HgB).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as Hd0.
  destruct Hd0 as (_ & _ & _ & _ & _ & _ & HF & _).
  destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hsok Hshi].
  pose proof (u_lt (lden E (rg_base R))) as Rb.
  assert (Hx : 0 <= x < two64) by (unfold uE in *; lia).
  destruct (dep_sep_f3_spec _ _ _ _ _ _ _ _ _ _ _ R eq_refl eq_refl Hok) as [Hxa|Hrest]; cbv beta in *; [discriminate Hxa|].
  destruct Hrest as [Hokb|Hgi].
  2:{ destruct (grant_in_pts E (s_facts L) (sm_maps M) model _ HF (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
                  (dn_gsh _ _ _ _ _ _ _ _ _ Hd) jD1 jB1 R Hgi x Hw) as (Hcov & _ & Hdj).
      destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]].
      - pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hcov) as Hnr. rewrite (res_pts model (dn_res _ _ _ _ _ _ _ _ _ Hd) x (or_introl D)) in Hnr. discriminate.
      - pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hcov) as Hnr. rewrite (res_pts model (dn_res _ _ _ _ _ _ _ _ _ Hd) x (or_intror D)) in Hnr. discriminate.
      - apply (Hdj jD1 _ HgD (find_grant_nomark _ _ _ _ HD1 _) (or_introl eq_refl)). cbn [fst snd]. unfold gsz. cbn [fst snd].
        replace (uE E (lconst 1048576)) with 1048576 by (unfold uE; rewrite lden_lconst; symmetry; apply u_small64; unfold two64; lia). exact D.
      - apply (Hdj jB1 _ HgB (find_grant_nomark _ _ _ _ HB1 _) (or_intror eq_refl)). cbn [fst snd]. unfold gsz. cbn [fst snd].
        replace (uE E (lconst 8388608)) with 8388608 by (unfold uE; rewrite lden_lconst; symmetry; apply u_small64; unfold two64; lia). exact D. }
  assert (Hbnd : Forall (fun R0 => 0 <= rsz E R0 /\ uE E (rg_base R0) + rsz E R0 <= two64) [R]) by (constructor; [split; [exact P1 | exact P2] | constructor]).
  assert (Hok1 : forallb (dep_sep_b (s_facts L) (sm_maps M) (vm_reserved (m_vmmaps model)) jD1 jB1 (sm_sp M) (fst (a_dep a)) (snd (a_dep a))) [R] = true).
  { cbn [forallb]. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd). fold ASEGSR. rewrite Hokb. reflexivity. }
  pose proof (dep_outside_rgs E (s_facts L) (sm_maps M) model (sm_sp M) _ HF (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
         (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) Hshi Hsok (dn_mres _ _ _ _ _ _ _ _ _ Hd)
         (dn_res _ _ _ _ _ _ _ _ _ Hd) [R] jD1 jB1 _ _ (fst (a_dep a)) (snd (a_dep a)) Hbnd HgD eq_refl eq_refl HgB eq_refl eq_refl (find_grant_nomark _ _ _ _ HD1 _) (find_grant_nomark _ _ _ _ HB1 _) Hok1 x Hx Hdw) as Ho.
  unfold outside in Ho. pose proof (Forall_inv Ho) as Hp. cbv beta in Hp. rewrite u_small64 in Hp by exact Hx. unfold uE in Hw. lia.
Qed.
Definition a_inc (a : ast) : ast := AST (a_on a) (a_rgs a) (a_fcts a) (a_own a) (a_dep a) (laddc (a_nl a) 1) (a_live a) (a_pri a).
#[using="Type"] Lemma HA_put : forall n E E' M a m0 m0' nd' F' st', HA_on E M a m0 -> sm_wf n M = true -> awf n a = true -> agree n E E' ->
  INV_D m0' (dD1 E a) (dB1 E a) nd' F' st' -> nd' <= 1 + (uE E (a_nl a) + 1) -> F' <= 3 + 31 * (uE E (a_nl a) + 1) -> uE E (a_nl a) < 33000 ->
  (a_pri a <> [] -> forall x, pri_foot E a x -> m0' (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) ->
  HA_on E' M (a_inc a) m0'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' M a m0 m0' nd' F' st' HA Hwf Haw Ha HI Hn HF Hl Hsp. destruct HA as [Hdep Hown Hownx Hhi HgD HgB Hpri].
  assert (Hpw : pwf n (a_dep a) = true) by (pose proof Haw as X; unfold awf in X; apply andb_prop in X as [X _]; apply andb_prop in X as [X _]; apply andb_prop in X as [_ X]; exact X).
  pose proof (awf_nl n a Haw) as Hlw.
  unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2].
  assert (E1 : dD1 E' (a_inc a) = dD1 E a) by (unfold dD1; cbn [a_inc a_dep]; exact (uE_agree n E E' _ Hp1 Ha)).
  assert (E2 : dB1 E' (a_inc a) = dB1 E a) by (unfold dB1; cbn [a_inc a_dep]; exact (uE_agree n E E' _ Hp2 Ha)).
  destruct Hdep as (nd & F & st & _ & _ & _ & Hl0).
  assert (E0 : uE E' (a_nl (a_inc a)) = uE E (a_nl a) + 1).
  { cbn [a_inc a_nl]. rewrite (uE_laddc2 E' (a_nl a) 1) by (rewrite ?(uE_agree n E E' _ Hlw Ha); unfold two64; lia). rewrite (uE_agree n E E' _ Hlw Ha). reflexivity. }
  constructor; rewrite ?E1, ?E2, ?E0.
  - exists nd', F', st'. split; [exact HI|]. lia.
  - intros x Hx Hdw. apply (proj2 (own_pt_agree n E E' M x Hwf Ha)). exact (Hown x Hx Hdw).
  - exact Hownx.
  - exact Hhi.
  - exact HgD.
  - exact HgB.
  - intros Hne. cbn [a_inc a_pri] in Hne.
    pose proof (PRI_on_agree n E E' M a m0 Hwf Haw Ha (Hpri Hne)) as [Hi Hox Hp Ht Hz Hs Hxt Hlv Hsd].
    assert (Epd : pden E' a = pden E a) by exact (pden_agree n E E' a Haw Ha).
    constructor.
    + unfold INV_A in *. change (pden E' (a_inc a)) with (pden E' a). apply (INV_Az_frame _ m0); [|exact Hi].
      intros x Hx. apply (Hsp Hne). unfold pri_foot. rewrite <- Epd. exact Hx.
    + exact Hox.
    + exact Hp.
    + exact Ht.
    + exact Hz.
    + exact Hs.
    + exact Hxt.
    + (* [comment removed for export] *)
      apply (lv_inv_mono E' E' a (a_inc a) m0 m0'); [intros i; reflexivity | reflexivity | intros b z X; exact X | | exact Hlv].
      intros b z Hs0 x Hx. apply (Hsp Hne). unfold pri_foot. rewrite <- Epd. exact (ext_sem_foot _ m0 b z Hi Hs0 x Hx).
    + exact Hsd.
Qed.
#[using="Type"] Lemma ecall_73aa8 : tlookup ATBLd 0x73c44 = XEcall.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma HA_maps : forall E M M' a m0, HA_on E M a m0 -> sm_own M' = sm_own M -> sm_zr M' = sm_zr M ->
  (forall b z k, In (b, z, k) (sm_maps M) -> exists k', In (b, z, k') (sm_maps M')) -> HA_on E M' a m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M M' a m0 HA Ho Hzr Hm. destruct HA as [Hdep Hown Hownx Hhi HgD HgB Hpri]. constructor.
  - exact Hdep.
  - intros x Hx Hdw. destruct (Hown x Hx Hdw) as (q & Hq & Hw). exists q. rewrite Ho. split; [exact Hq | exact Hw].
  - exact Hownx.
  - exact Hhi.
  - destruct HgD as (k & Hk). exact (Hm _ _ _ Hk).
  - destruct HgB as (k & Hk). exact (Hm _ _ _ Hk).
  - intros Hne. destruct (Hpri Hne) as [Hi Hox (kp & Hp) (kt & Ht) Hz Hs Hxt Hlv Hsd]. constructor.
    + exact Hi.
    + intros x Hx Hf. destruct (Hox x Hx Hf) as (q & Hq & Hw). exists q. rewrite Ho. split; [exact Hq | exact Hw].
    + exact (Hm _ _ _ Hp).
    + exact (Hm _ _ _ Ht).
    + intros x Hx. rewrite Hzr. exact (Hz x Hx).
    + exact Hs.
    + exact Hxt.
    + exact Hlv.
    + exact Hsd.
Qed.
(* [comment removed for export] *)
Definition has_g (gs : list (lin * lin * gkind)) (b : lin) (z : Z) : bool :=
  existsb (fun g => lin_eqb (fst (fst g)) b && lin_eqb (snd (fst g)) (lconst z))%bool gs.
#[using="Type"] Lemma has_g_In : forall gs b z, has_g gs b z = true -> exists k, In (b, lconst z, k) gs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros gs b z H. unfold has_g in H. apply existsb_exists in H as (g & Hg & Hc). apply andb_prop in Hc as [H1 H2]. apply lin_eqb_eq in H1, H2.
  exists (snd g). destruct g as [[b' z'] k']. cbn [fst snd] in *. subst. exact Hg.
Qed.
Definition amod_a (M M' : smodel) (a : ast) : bool :=
  (negb (a_on a) ||
   (list_eqb pair_eqb (sm_own M') (sm_own M) && zr_eqb (sm_zr M') (sm_zr M) &&
    has_g (sm_maps M') (fst (a_dep a)) 1048576 && has_g (sm_maps M') (snd (a_dep a)) 8388608 &&
    match a_pri a with [] => true | _ => has_g (sm_maps M') (p_pg a) PG_SIZE && has_g (sm_maps M') (p_tg a) TG_SIZE end))%bool.
#[using="Type"] Theorem alloc_HA_mod : forall E M M' a m0, amod_a M M' a = true -> HA E M a m0 -> HA E M' a m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M M' a m0 H HA0 Hon. specialize (HA0 Hon). unfold amod_a in H. rewrite Hon in H. cbn [negb orb] in H.
  apply andb_prop in H as [H Hp]. apply andb_prop in H as [H HB]. apply andb_prop in H as [H HD]. apply andb_prop in H as [Ho Hz].
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ho. apply zr_eqb_eq in Hz.
  destruct HA0 as [Hdep Hown Hownx Hhi HgD HgB Hpri]. constructor.
  - exact Hdep.
  - intros x Hx Hdw. destruct (Hown x Hx Hdw) as (q & Hq & Hw). exists q. rewrite Ho. split; [exact Hq | exact Hw].
  - exact Hownx.
  - exact Hhi.
  - exact (has_g_In _ _ _ HD).
  - exact (has_g_In _ _ _ HB).
  - intros Hne. destruct (Hpri Hne) as [Hi Hox _ _ Hzz Hs Hxt Hlv Hsd]. destruct (a_pri a) as [|p0 pr] eqn:Hap; [exfalso; exact (Hne eq_refl)|].
    apply andb_prop in Hp as [Hp1 Hp2]. constructor.
    + exact Hi.
    + intros x Hx Hf. destruct (Hox x Hx Hf) as (q & Hq & Hw). exists q. rewrite Ho. split; [exact Hq | exact Hw].
    + exact (has_g_In _ _ _ Hp1).
    + exact (has_g_In _ _ _ Hp2).
    + intros x Hx. rewrite Hz. exact (Hzz x Hx).
    + exact Hs.
    + exact Hxt.
    + exact Hlv.
    + exact Hsd.
Qed.
#[using="Type"] Lemma in_set_kind : forall gs j k b z kd, In (b, z, kd) gs -> exists k', In (b, z, k') (set_kind j k gs).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction gs as [|g r IH]; intros j k b z kd H; [destruct H|]. destruct H as [->|H].
  - destruct j as [|j]; cbn [set_kind]; [exists k; left; reflexivity | exists kd; left; reflexivity].
  - destruct j as [|j]; cbn [set_kind]; [exists kd; right; exact H|]. destruct (IH j k b z kd H) as (k' & Hk'). exists k'. right. exact Hk'.
Qed.
#[using="Type"] Lemma HA_on_agree : forall n E E' M a m0, HA_on E M a m0 -> sm_wf n M = true -> awf n a = true -> agree n E E' -> HA_on E' M a m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' M a m0 HA Hwf Haw Ha.
  assert (Hpw : pwf n (a_dep a) = true) by (pose proof Haw as X; unfold awf in X; apply andb_prop in X as [X _]; apply andb_prop in X as [X _]; apply andb_prop in X as [_ X]; exact X).
  pose proof (awf_nl n a Haw) as Hlw.
  destruct HA as [Hdep Hown Hownx Hhi HgD HgB Hpri].
  assert (E0 : uE E' (a_nl a) = uE E (a_nl a)) by (exact (uE_agree n E E' _ Hlw Ha)).
  unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2].
  assert (E1 : dD1 E' a = dD1 E a) by (unfold dD1; exact (uE_agree n E E' _ Hp1 Ha)).
  assert (E2 : dB1 E' a = dB1 E a) by (unfold dB1; exact (uE_agree n E E' _ Hp2 Ha)).
  constructor; rewrite ?E1, ?E2, ?E0.
  - exact Hdep.
  - intros x Hx Hdw. apply (proj2 (own_pt_agree n E E' M x Hwf Ha)). exact (Hown x Hx Hdw).
  - exact Hownx.
  - exact Hhi.
  - exact HgD.
  - exact HgB.
  - intros Hne. exact (PRI_on_agree n E E' M a m0 Hwf Haw Ha (Hpri Hne)).
Qed.
#[using="Type"] Lemma frz_same_agree : forall n E E' M M1 m0 m0', sm_wf n M1 = true -> sm_frz M = sm_frz M1 -> agree n E E' ->
  frz_same E' M m0 m0' -> frz_same E M m0 m0'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' M M1 m0 m0' Hwf Hfr Ha H p Hp w Hw. apply (H p Hp w).
  unfold sm_wf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?]).
  match goal with X : forallb (fun p => (lwf n (fst p) && lwf n (snd p))%bool) (sm_frz M1) = true |- _ => rename X into Hf end.
  rewrite forallb_forall in Hf. rewrite Hfr in Hp. destruct (andb_prop _ _ (Hf p Hp)) as [P1 P2].
  rewrite (uE_agree n E E' _ P1 Ha), (uE_agree n E E' _ P2 Ha). exact Hw.
Qed.

End MALlib.
