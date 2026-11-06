(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChFix FxChSep FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA AcEntry AcCarve AcConv AcConvInvLib AcConvInvG AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcConvLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvLib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvInvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvLib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint find_rg_acc' (f : region -> bool) (rgs : list region) (i : nat) : option nat :=
  match rgs with [] => None | R :: r => if f R then Some i else find_rg_acc' f r (Datatypes.S i) end.

Definition conv_nl (Rt Rs : region) : Z :=
  match cword (rg_cont Rt) 4197528 4, cword (rg_cont Rs) 3208 8 with Some n, Some F => Z.max (n - 1) ((F - 3 + 30) / 31) | _, _ => 0 end.
Definition conv_ok_g (S : sst) (M : smodel) (q : convp) (Rt Rs Rd Rb : region) : bool :=
  let D1l := rg_base Rd in let B1l := rg_base Rb in
  match find_grant (sm_maps M) D1l 1048576, find_grant (sm_maps M) B1l 8388608, cword (rg_cont Rt) 4197528 4, cword (rg_cont Rs) 3208 8,
        cword (rg_cont Rs) 3232 4 with
  | Some jD, Some jB, Some n, Some F, Some st =>
      (rg_tab_b Rt && rg_ss_b Rs && rg_big_b Rd 1048576 && rg_big_b Rb 8388608 &&
       tab_ok_g (rg_cont Rt) (rg_cont Rd) n (Datatypes.S (Z.to_nat n)) && fb (rg_cont Rt) (bv_list 4197544 D1l 8) && fb (rg_cont Rs) (bv_list 3224 B1l 8) &&
       Z.leb 0 n && Z.leb n 65533 && Z.leb 0 st && Z.leb st F && Z.leb F 1048000 &&
       Z.leb n (1 + conv_nl Rt Rs) && Z.leb F (3 + 31 * conv_nl Rt Rs) && Z.leb 0 (conv_nl Rt Rs) && Z.leb (conv_nl Rt Rs) 33000 &&
       negb (Nat.eqb jD jB) && sep_noshadow_b (s_facts S) Rd && sep_noshadow_b (s_facts S) Rb &&
       lwf (s_next S) D1l && lwf (s_next S) B1l && perm_ix_ok (length (s_rgs S)) (conv_ix (length (s_rgs S)) q))%bool
  | _, _, _, _, _ => false
  end.

Definition apost_conv_g (q : convp) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (anil a && sm_own_nil M)%bool (
  obind (nth_error (s_rgs S) (cq_tab q)) (fun Rt =>
  obind (nth_error (s_rgs S) (cq_ss q)) (fun Rs =>
  obind (nth_error (s_rgs S) (cq_d1 q)) (fun Rd =>
  obind (nth_error (s_rgs S) (cq_b1 q)) (fun Rb =>
  obool (conv_ok_g S M q Rt Rs Rd Rb) (
  Some (with_rgs S (List.map (fun k => nth k (s_rgs S) (RG lc0 lc0 RW TEmpty)) (keep_ix (length (s_rgs S)) q)),
        with_own M (own_of (rg_base Rd) (rg_base Rb)),
        AST true [] [] (own_of (rg_base Rd) (rg_base Rb)) (rg_base Rd, rg_base Rb) (lconst (conv_nl Rt Rs)) [] []))))))).
Lemma apost_conv_g_unf : forall q S M a,
  obool (anil a && sm_own_nil M)%bool (
  obind (nth_error (s_rgs S) (cq_tab q)) (fun Rt =>
  obind (nth_error (s_rgs S) (cq_ss q)) (fun Rs =>
  obind (nth_error (s_rgs S) (cq_d1 q)) (fun Rd =>
  obind (nth_error (s_rgs S) (cq_b1 q)) (fun Rb =>
  obool (conv_ok_g S M q Rt Rs Rd Rb) (
  Some (with_rgs S (List.map (fun k => nth k (s_rgs S) (RG lc0 lc0 RW TEmpty)) (keep_ix (length (s_rgs S)) q)),
        with_own M (own_of (rg_base Rd) (rg_base Rb)),
        AST true [] [] (own_of (rg_base Rd) (rg_base Rb)) (rg_base Rd, rg_base Rb) (lconst (conv_nl Rt Rs)) [] []))))))) = apost_conv_g q S M a.
Proof. intros. exact eq_refl. Qed.

Section Conv.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_above_image : forall mem0 E S M ms model g, DEN ASEGS LIMIT model0 mem0 E S M ms model -> In g (sm_maps M) -> is_mark g = false -> 65536 <= gsz E g ->
  6529024 <= uE E (fst (fst g)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S M ms model g Hd Hg Hgm Hz.
  pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs. destruct (Hgs g Hg) as (G1 & G2 & G3 & G4 & G5).
  destruct (Z_lt_ge_dec (uE E (fst (fst g))) 6529024) as [Hlt|]; [|lia]. exfalso.
  set (x := Z.max (uE E (fst (fst g))) 65536).
  assert (Hc1 : covered (vm_maps (m_vmmaps model)) x = true).
  { apply (grant_covered E _ M model g (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_gsh _ _ _ _ _ _ _ _ _ Hd) Hg Hgm). unfold x. lia. }
  pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hc1) as Hc2. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd) in Hc2.
  rewrite (res_cov x ltac:(unfold x; lia)) in Hc2. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grants_apart : forall mem0 E S M ms model i j gi gj, DEN ASEGS LIMIT model0 mem0 E S M ms model ->
  nth_error (sm_maps M) i = Some gi -> nth_error (sm_maps M) j = Some gj -> i <> j -> is_mark gi = false -> is_mark gj = false ->
  uE E (fst (fst gi)) + gsz E gi <= uE E (fst (fst gj)) \/ uE E (fst (fst gj)) + gsz E gj <= uE E (fst (fst gi)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E S M ms model i j gi gj Hd Hi Hj Hij Hmi Hmj.
  pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd. rewrite (dn_maps _ _ _ _ _ _ _ _ _ Hd) in Hpd.
  pose proof (pdisj_lden_nth E _ _ i j gi gj Hpd Hi Hj Hij Hmi Hmj) as Hdj.
  pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs.
  destruct (Hgs gi (nth_error_In _ _ Hi)) as (A1 & _ & _ & A4 & _). destruct (Hgs gj (nth_error_In _ _ Hj)) as (B1 & _ & _ & B4 & _).
  assert (Ui : 0 <= uE E (fst (fst gi))) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E (fst (fst gi)))) as X; unfold bv_modulus in X; lia).
  assert (Uj : 0 <= uE E (fst (fst gj))) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E (fst (fst gj)))) as X; unfold bv_modulus in X; lia).
  unfold iv_disj, gden, FxBacking.B, FxBacking.S in Hdj. cbn [fst snd] in Hdj. unfold gsz, uE. exact Hdj.
Qed.

#[using="Type"] Theorem conv_g_node : forall q S M a S' M' a', apost_conv_g q S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros q S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_conv_g_unf in H.
  apply obool_some in H as (Hnil & H). apply andb_prop in Hnil as [_ Hown0].
  apply obind_some in H as (Rt & HRt & H). cbv beta in H.
  apply obind_some in H as (Rs & HRs & H). cbv beta in H.
  apply obind_some in H as (Rd & HRd & H). cbv beta in H.
  apply obind_some in H as (Rb & HRb & H). cbv beta in H.
  apply obool_some in H as (Hok & H). injection H as <- <- <-.
  assert (Hown : sm_own M = []) by (unfold sm_own_nil in Hown0; destruct (sm_own M); [reflexivity | discriminate]).
  unfold conv_ok_g in Hok.
  destruct (find_grant (sm_maps M) (rg_base Rd) 1048576) as [jD|] eqn:HjD; [|discriminate].
  destruct (find_grant (sm_maps M) (rg_base Rb) 8388608) as [jB|] eqn:HjB; [|discriminate].
  destruct (cword (rg_cont Rt) 4197528 4) as [nn|] eqn:Hnn; [|discriminate].
  destruct (cword (rg_cont Rs) 3208 8) as [FF|] eqn:HFF; [|discriminate].
  destruct (cword (rg_cont Rs) 3232 4) as [stt|] eqn:Hstt; [|discriminate].
  repeat (apply andb_prop in Hok as [Hok ?]).
  match goal with H : perm_ix_ok _ _ = true |- _ => rename H into Hperm end.
  match goal with H : lwf _ (rg_base Rb) = true |- _ => rename H into HwB end.
  match goal with H : lwf _ (rg_base Rd) = true |- _ => rename H into HwD end.
  match goal with H : sep_noshadow_b _ Rb = true |- _ => rename H into HnsB end.
  match goal with H : sep_noshadow_b _ Rd = true |- _ => rename H into HnsD end.
  match goal with H : negb (Nat.eqb jD jB) = true |- _ => rename H into Hne end.
  match goal with H : fb (rg_cont Rs) _ = true |- _ => rename H into HsD end.
  match goal with H : fb (rg_cont Rt) _ = true |- _ => rename H into HmapT end.
  match goal with H : tab_ok_g _ _ _ _ = true |- _ => rename H into Htabc end.
  repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end.
  match goal with H : rg_big_b Rb _ = true |- _ => rename H into HbB end.
  match goal with H : rg_big_b Rd _ = true |- _ => rename H into HbD end.
  match goal with H : rg_ss_b Rs = true |- _ => rename H into HsS end.
  rename Hok into HtT.
  apply negb_true_iff, Nat.eqb_neq in Hne.
  destruct (find_grant_sound _ _ _ _ HjD) as (kD & HgD). destruct (find_grant_sound _ _ _ _ HjB) as (kB & HgB).
  pose proof (rg_tab_sound Rt HtT) as ERt. pose proof (rg_ss_sound Rs HsS) as ERs.
  pose proof (rg_big_sound Rd _ HbD) as ERd. pose proof (rg_big_sound Rb _ HbB) as ERb.
  set (D1l := rg_base Rd) in *. set (B1l := rg_base Rb) in *.
  set (keep := List.map (fun k => nth k (s_rgs S) (RG lc0 lc0 RW TEmpty)) (keep_ix (length (s_rgs S)) q)) in *.
  set (own' := own_of D1l B1l) in *.
  (* [comment removed for export] *)
  assert (Hmap : List.map (fun k => nth k (s_rgs S) (RG lc0 lc0 RW TEmpty)) (conv_ix (length (s_rgs S)) q) = keep ++ [Rt; Rs; Rd; Rb]).
  { unfold conv_ix. rewrite map_app. f_equal. unfold cq_list. cbn [List.map].
    rewrite (nth_error_nth _ _ _ HRt), (nth_error_nth _ _ _ HRs), (nth_error_nth _ _ _ HRd), (nth_error_nth _ _ _ HRb). reflexivity. }
  pose proof (perm_ix_sound (s_rgs S) (RG lc0 lc0 RW TEmpty) _ Hperm) as HP. rewrite Hmap in HP.
  pose proof (den_perm ASEGS LIMIT model0 mem0 E S M ms model _ Hd HP) as Hd1.
  (* [comment removed for export] *)
  pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs.
  destruct (Hgs _ (nth_error_In _ _ HgD)) as (GD1 & GD2 & GD3 & GD4 & GD5). destruct (Hgs _ (nth_error_In _ _ HgB)) as (GB1 & GB2 & GB3 & GB4 & GB5).
  assert (ZD : gsz E (D1l, lconst 1048576, kD) = 1048576) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold two64; lia).
  assert (ZB : gsz E (B1l, lconst 8388608, kB) = 8388608) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold two64; lia).
  rewrite ?ZD in GD1, GD2, GD3, GD4, GD5. rewrite ?ZB in GB1, GB2, GB3, GB4, GB5.
  cbn [fst snd] in GD1, GD2, GD3, GD4, GD5, GB1, GB2, GB3, GB4, GB5.
  pose proof (grant_above_image mem0 E S M ms model _ Hd (nth_error_In _ _ HgD) (is_mark_csize _ _ _) ltac:(rewrite ZD; lia)) as HiD. cbn [fst] in HiD.
  pose proof (grant_above_image mem0 E S M ms model _ Hd (nth_error_In _ _ HgB) (is_mark_csize _ _ _) ltac:(rewrite ZB; lia)) as HiB. cbn [fst] in HiB.
  pose proof (grants_apart mem0 E S M ms model _ _ _ _ Hd HgD HgB Hne (is_mark_csize _ _ _) (is_mark_csize _ _ _)) as Hap. rewrite ZD, ZB in Hap. cbn [fst snd] in Hap.
  (* [comment removed for export] *)
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as Hd0. destruct Hd0 as (_ & _ & _ & _ & Hrgs & _ & HF & _).
  rewrite Forall_forall in Hrgs.
  set (H := Hof E M model) in *.
  pose proof (Hrgs _ (nth_error_In _ _ HRt)) as RT. pose proof (Hrgs _ (nth_error_In _ _ HRs)) as RS.
  pose proof (Hrgs _ (nth_error_In _ _ HRd)) as RD. pose proof (Hrgs _ (nth_error_In _ _ HRb)) as RB.
  rewrite ERt in RT. rewrite ERs in RS. rewrite ERd in RD. rewrite ERb in RB.
  assert (HI0 : INV_D (ms_mem (restrict H ms)) (uE E D1l) (uE E B1l) nn FF stt).
  { apply (inv_d_main_g E _ D1l B1l (rg_cont Rt) (rg_cont Rs) (rg_cont Rd) (rg_cont Rb) nn FF stt _ RT RS RD RB Htabc Hnn ltac:(lia) HmapT HFF Hstt ltac:(lia) HsD).
    - split; [exact HiD|]. split; [lia | exact (mod4096_16 _ GD3)].
    - split; [exact HiB|]. split; [lia | exact (mod4096_8 _ GB3)].
    - exact Hap. }
  (* [comment removed for export] *)
  assert (Hwo : forallb (fun p => lwf (s_next (with_rgs S (keep ++ [Rt; Rs; Rd; Rb]))) (fst p) && lwf (s_next (with_rgs S (keep ++ [Rt; Rs; Rd; Rb]))) (snd p))%bool own' = true).
  { cbn [with_rgs s_next]. unfold own', own_of. cbn [forallb fst snd]. rewrite HwD, HwB. reflexivity. }
  assert (U1 : uE E (lconst 1859584) = 1859584) by (apply uE_lconst'; unfold two64; lia).
  assert (U2 : uE E (lconst 4198400) = 4198400) by (apply uE_lconst'; unfold two64; lia).
  assert (U3 : uE E (lconst 1794048) = 1794048) by (apply uE_lconst'; unfold two64; lia).
  assert (U4 : uE E (lconst 4096) = 4096) by (apply uE_lconst'; unfold two64; lia).
  assert (U5 : uE E (lconst 1048576) = 1048576) by (apply uE_lconst'; unfold two64; lia).
  assert (U6 : uE E (lconst 8388608) = 8388608) by (apply uE_lconst'; unfold two64; lia).
  assert (Z1 : rsz E Rt = 4198400) by (rewrite ERt; apply rsz_lconst'; unfold two64; lia).
  assert (Z2 : rsz E Rs = 4096) by (rewrite ERs; apply rsz_lconst'; unfold two64; lia).
  assert (Z3 : rsz E Rd = 1048576) by (rewrite ERd; apply rsz_lconst'; unfold two64; lia).
  assert (Z4 : rsz E Rb = 8388608) by (rewrite ERb; apply rsz_lconst'; unfold two64; lia).
  assert (B1' : uE E (rg_base Rt) = 1859584) by (rewrite ERt; exact U1).
  assert (B2' : uE E (rg_base Rs) = 1794048) by (rewrite ERs; exact U3).
  pose proof (den_drop_own ASEGS LIMIT model0 mem0 E (with_rgs S (keep ++ [Rt; Rs; Rd; Rb])) M ms model keep [Rt; Rs; Rd; Rb] own' Hd1 eq_refl Hown Hwo) as Hd2.
  assert (Hd3 : DEN ASEGS LIMIT model0 (ms_mem ms) E (with_rgs S keep) (with_own M own') ms model).
  { apply Hd2.
    - intros pp w Hp Hw. unfold own', own_of in Hp. cbn [In] in Hp.
      assert (Hw64 : 0 <= w < two64).
      { destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hw; rewrite ?U1, ?U2, ?U3, ?U4, ?U5, ?U6 in Hw; unfold two64; unfold D1l, B1l in *; lia. }
      destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hw; rewrite ?U1, ?U2, ?U3, ?U4, ?U5, ?U6 in Hw.
      + exists Rt. split; [left; reflexivity|]. unfold in_rg. fold (uE E (rg_base Rt)). rewrite B1', Z1, u_small64 by exact Hw64. lia.
      + exists Rs. split; [right; left; reflexivity|]. unfold in_rg. fold (uE E (rg_base Rs)). rewrite B2', Z2, u_small64 by exact Hw64. lia.
      + exists Rd. split; [right; right; left; reflexivity|]. unfold in_rg. fold (uE E (rg_base Rd)). rewrite Z3, u_small64 by exact Hw64. unfold D1l in Hw. lia.
      + exists Rb. split; [right; right; right; left; reflexivity|]. unfold in_rg. fold (uE E (rg_base Rb)). rewrite Z4, u_small64 by exact Hw64. unfold B1l in Hw. lia.
    - intros R x HR Hx. unfold in_rg in Hx. fold (uE E (rg_base R)) in Hx. cbn [In] in HR.
      destruct HR as [<-|[<-|[<-|[<-|[]]]]].
      + exists (lconst 1859584, lconst 4198400). split; [left; reflexivity|]. cbn [fst snd]. rewrite U1, U2. rewrite B1', Z1 in Hx. exact Hx.
      + exists (lconst 1794048, lconst 4096). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite U3, U4. rewrite B2', Z2 in Hx. exact Hx.
      + exists (D1l, lconst 1048576). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite U5. rewrite Z3 in Hx. exact Hx.
      + exists (B1l, lconst 8388608). split; [right; right; right; left; reflexivity|]. cbn [fst snd]. rewrite U6. rewrite Z4 in Hx. exact Hx. }
  (* [comment removed for export] *)
  assert (HI : INV_D (ms_mem ms) (uE E D1l) (uE E B1l) nn FF stt).
  { apply (INV_D_frame _ _ _ _ _ _ _ HI0). intros x Hx Hdw.
    assert (Hin : exists R, In R [Rt; Rs; Rd; Rb] /\ in_rg E R (Z_to_bv 64 x)).
    { unfold downed in Hdw. unfold in_rg. rewrite u_small64 by (unfold two64; lia).
      destruct Hdw as [X|[X|[X|[X|[X|X]]]]].
      - exists Rt. split; [left; reflexivity|]. fold (uE E (rg_base Rt)). rewrite B1', Z1. lia.
      - exists Rt. split; [left; reflexivity|]. fold (uE E (rg_base Rt)). rewrite B1', Z1. lia.
      - exists Rt. split; [left; reflexivity|]. fold (uE E (rg_base Rt)). rewrite B1', Z1. lia.
      - exists Rd. split; [right; right; left; reflexivity|]. fold (uE E (rg_base Rd)). rewrite Z3. unfold D1l in X. lia.
      - exists Rs. split; [right; left; reflexivity|]. fold (uE E (rg_base Rs)). rewrite B2', Z2. lia.
      - exists Rb. split; [right; right; right; left; reflexivity|]. fold (uE E (rg_base Rb)). rewrite Z4. unfold B1l in X. lia. }
    destruct Hin as (R & HR & Hx').
    assert (HRin : In R (s_rgs S)).
    { cbn [In] in HR. destruct HR as [<-|[<-|[<-|[<-|[]]]]]; [exact (nth_error_In _ _ HRt) | exact (nth_error_In _ _ HRs) | exact (nth_error_In _ _ HRd) | exact (nth_error_In _ _ HRb)]. }
    pose proof (vis_of_rg ASEGS E H (ms_mem ms) R _ (dn_hoff _ _ _ _ _ _ _ _ _ Hd) (Hrgs R HRin) Hx') as Hvis.
    unfold wa. cbn [restrict ms_mem] in *. unfold mrestrict. rewrite Hvis. reflexivity. }
  apply (Hk E (ms_mem ms) ms model (agree_refl _ _)); [| exact Hd3 |].
  - intros pp Hp w Hw. destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd pp Hp w Hw) as (_ & _ & X). exact X.
  - intros _. constructor.
    + exists nn, FF, stt. unfold dD1, dB1. cbn [a_dep fst snd a_nl]. split; [exact HI|]. rewrite uE_lc by lia. lia.
    + intros x Hx Hdw. unfold own_pt. cbn [with_own sm_own]. unfold dD1, dB1 in Hdw. cbn [a_dep fst snd] in Hdw. unfold downed in Hdw.
      unfold own', own_of. destruct Hdw as [X|[X|[X|[X|[X|X]]]]].
      * exists (lconst 1859584, lconst 4198400). split; [left; reflexivity|]. cbn [fst snd]. rewrite U1, U2. lia.
      * exists (lconst 1859584, lconst 4198400). split; [left; reflexivity|]. cbn [fst snd]. rewrite U1, U2. lia.
      * exists (lconst 1859584, lconst 4198400). split; [left; reflexivity|]. cbn [fst snd]. rewrite U1, U2. lia.
      * exists (D1l, lconst 1048576). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite U5. lia.
      * exists (lconst 1794048, lconst 4096). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite U3, U4. lia.
      * exists (B1l, lconst 8388608). split; [right; right; right; left; reflexivity|]. cbn [fst snd]. rewrite U6. lia.
    + reflexivity.
    + unfold dD1, dB1. cbn [a_dep fst snd]. split.
      * apply (noshadow_range (uE E D1l) 1048576 ltac:(lia)). intros w Hw. apply (noshadow_sound E _ Rd HF HnsD). rewrite Z3. exact Hw.
      * apply (noshadow_range (uE E B1l) 8388608 ltac:(lia)). intros w Hw. apply (noshadow_sound E _ Rb HF HnsB). rewrite Z4. exact Hw.
    + exists kD. cbn [with_own sm_maps a_dep fst]. exact (nth_error_In _ _ HgD).
    + exists kB. cbn [with_own sm_maps a_dep snd]. exact (nth_error_In _ _ HgB).
    + intros Hpn. exfalso. apply Hpn. reflexivity.
Qed.



(* [comment removed for export] *)
Definition d1_lin (c : tree bval) : option lin := match tget (okey 4197544) c with Some (BV l 0) => Some l | _ => None end.
Definition b1_lin (c : tree bval) : option lin := match tget (okey 3224) c with Some (BV l 0) => Some l | _ => None end.
Definition find_conv (S : sst) : option convp :=
  obind (find_rg_acc' rg_tab_b (s_rgs S) O) (fun it =>
  obind (find_rg_acc' rg_ss_b (s_rgs S) O) (fun iss =>
  obind (nth_error (s_rgs S) it) (fun Rt =>
  obind (nth_error (s_rgs S) iss) (fun Rs =>
  obind (d1_lin (rg_cont Rt)) (fun D1l =>
  obind (b1_lin (rg_cont Rs)) (fun B1l =>
  obind (find_rg_acc' (fun R => rg_big_b R 1048576 && lin_eqb (rg_base R) D1l)%bool (s_rgs S) O) (fun id =>
  obind (find_rg_acc' (fun R => rg_big_b R 8388608 && lin_eqb (rg_base R) B1l)%bool (s_rgs S) O) (fun ib =>
  Some (CONVP it iss id ib))))))))).
Definition apost_convG (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) := obind (find_conv S) (fun q => apost_conv_g q S M a).
#[using="Type"] Theorem convG_node : forall S M a S' M' a', apost_convG S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a S' M' a' H. unfold apost_convG in H. apply obind_some in H as (q & _ & H). cbv beta in H. exact (conv_g_node q S M a S' M' a' H).
Qed.
End Conv.
