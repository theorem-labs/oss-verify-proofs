(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.

Module AcFixS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition al_cand (a : lin) (p : lin * Z) : bool :=
  match l_t a, l_t (fst p) with [], [] => true | ta, tp => shares ta tp end.
Definition allow_cov_f (fs : list fact) (a : lin) (n : Z) (al : list (lin * Z)) : bool :=
  let f := fun p : lin * Z => contained_b fs a n (fst p) (snd p) &&& Z.leb (snd (irange fs (fst p)) + snd p) two64 &&& Z.ltb 0 n in
  if existsb_lz f (List.filter (al_cand a) al) then true else existsb_lz f (List.filter (fun p => negb (al_cand a p)) al).
Lemma existsb_split : forall {A} (f p : A -> bool) l,
  (if existsb f (List.filter p l) then true else existsb f (List.filter (fun x => negb (p x)) l)) = existsb f l.
Proof.
  intros A f p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter existsb]. destruct (p x) eqn:Hp; cbn [negb existsb].
  - destruct (f x); [reflexivity | exact IH].
  - destruct (existsb f (List.filter p l)) eqn:H1.
    + rewrite <- IH. destruct (f x); reflexivity.
    + destruct (f x); [reflexivity | exact IH].
Qed.
Lemma allow_cov_f_eq : forall fs a n al, allow_cov_f fs a n al = allow_cov fs a n al.
Proof. intros fs a n al. unfold allow_cov_f, allow_cov. cbv zeta. rewrite !existsb_lz_eq. apply existsb_split. Qed.

Definition fixkeep_ok_s (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (na : bool) (j : nat) (kd' : gkind) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in let ln := rget (s_regs L) (rkey a1r) in
  match a7c L, arg L 2, arg L 3, arg L 5, nth_error (sm_maps M) j with
  | Some c7, Some prot, Some flags, Some off, Some g =>
      (Z.eqb c7 222 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && len_ok fs ln n &&
       negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       (if na then mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else negb (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
             && mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       contained_b fs a n (fst (fst g)) (gsz_lo fs g) && lal_ok a (fst (fst g)) &&
       (gkind_eqb kd' GE || (gkind_eqb kd' (snd g) && negb (gkind_eqb kd' GN) && (na || mmap_noreserve_b (Z_to_bv 64 flags)))) &&
       Z.ltb n 4611686018427387904 &&
       (negb (mmap_noreserve_b (Z_to_bv 64 flags)) ||| allow_cov_f fs a n (sm_allow M)) &&
       (negb na ||| zr_sep_g fs (sm_maps M) j a n (sm_zr M)) && lwf (s_next L) a &&
       Z.leb (eager_sum (s_facts L) (set_kind j kd' (sm_maps M)) + allow_bound (sm_allow M)) LIMIT &&
       Z.leb (eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M) + (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) LIMIT &&
       negb (is_mark g))%bool        (* [comment removed for export] *)
  | _, _, _, _, _ => false
  end.
End AcFixS.

Module AcComm.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChLib FxChNull FxChFix FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tmap_tset : forall {A B} (f : A -> B) k v t, tmap f (tset k v t) = tset k (f v) (tmap f t).
Proof.
  intros A B f k. induction k as [k IH|k IH|]; intros v [|l w r]; cbn [tset tmap]; try reflexivity;
    rewrite ?IH; try reflexivity.
  all: cbn [tmap]; rewrite ?IH; reflexivity.
Qed.
Lemma rset_shift : forall n R k l, tmap (lshift n) (rset R k l) = rset (tmap (lshift n) R) k (lshift n l).
Proof. intros n R k l. unfold rset. destruct k; [apply tmap_tset | apply tmap_tset | reflexivity]. Qed.

Lemma cmp_succ : forall m, Pos.compare m (Pos.succ m) = Lt.
Proof. intros m. apply Pos.compare_lt_iff. lia. Qed.
Lemma NA_shift : forall n m, NA (n + m) = lshift n (NA m).
Proof.
  intros n m. unfold NA, lshift, ladd, lscale, lvar. cbn [l_c l_t tscale].
  change (w64 (65536 * 1)) with 65536. change (w64 (4096 * 1)) with 4096. cbn [Z.eqb].
  cbn [tadd]. rewrite !cmp_succ. cbn [tadd tshift List.map fst snd]. f_equal. rewrite Pos.add_succ_r. reflexivity.
Qed.
Lemma NP_shift : forall n m, NP (n + m) = lshift n (NP m).
Proof.
  intros n m. unfold NP, laddc, lshift, ladd, lscale, lvar. cbn [l_c l_t tscale].
  change (w64 (8192 * 1)) with 8192. change (w64 (512 * 1)) with 512. cbn [Z.eqb].
  cbn [tadd]. rewrite !cmp_succ. cbn [tadd tshift List.map fst snd]. f_equal. rewrite Pos.add_succ_r. reflexivity.
Qed.

Lemma rshift_RGz : forall n b z k, rshift n (RGz b z k TEmpty) = RGz (lshift n b) z k TEmpty.
Proof. intros n b z k. reflexivity. Qed.

Lemma null_post_mrg : forall n L S nZ vis piece,
  null_post (mrg (sst_shift n L) S) nZ vis piece = mrg (sst_shift n (null_post L nZ vis piece)) S.
Proof.
  intros n L S nZ vis piece. unfold null_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
  rewrite rset_shift, <- (NA_shift n (s_next L)). f_equal.
  - rewrite map_app, app_assoc. f_equal. f_equal. unfold null_rgs.
    destruct vis, piece; cbn [app List.map]; rewrite ?rshift_RGz, ?(NA_shift n (s_next L)), ?(NP_shift n (s_next L)); reflexivity.
  - rewrite map_app, app_assoc. f_equal. f_equal. unfold null_facts. cbn [List.map fshift].
    rewrite <- (NA_shift n (s_next L)).
    assert (E1 : lshift n (laddc (NA (s_next L)) (- SH_HI)) = laddc (NA (n + s_next L)) (- SH_HI)) by (rewrite NA_shift; reflexivity).
    rewrite E1. f_equal. f_equal. f_equal. f_equal. unfold lshift, lvar. cbn. rewrite Pos.add_succ_r. reflexivity.
  - rewrite !Pos.add_succ_r. reflexivity.
Qed.

Lemma fix_post_mrg : forall n L S a, fix_post (mrg (sst_shift n L) S) (lshift n a) = mrg (sst_shift n (fix_post L a)) S.
Proof. intros n L S a. unfold fix_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite rset_shift. reflexivity. Qed.
Lemma add_post_mrg : forall n L S a z pc,
  add_post (mrg (sst_shift n L) S) (lshift n a) z (option_map (lshift n) pc) = mrg (sst_shift n (add_post L a z pc)) S.
Proof.
  intros n L S a z pc. unfold add_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
  rewrite map_app, app_assoc. f_equal. unfold add_rgs. destruct pc; reflexivity.
Qed.
Lemma rget_mrg : forall n L S k, rget (s_regs (mrg (sst_shift n L) S)) k = lshift n (rget (s_regs L) k).
Proof. intros n L S k. unfold mrg, sst_shift. cbn [s_regs]. apply rget_shift. Qed.
(* [comment removed for export] *)
End AcComm.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma page_in_ms_inside : forall l (lo hi : Z) (p : word), ivs_wf l ->
  lo <= bv_unsigned p -> bv_unsigned p + 4096 <= hi -> page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi p Hwf Hlo Hhi; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. unfold page_in_ranges in *. cbn [maps_subtract]. rewrite existsb_app.
  rewrite (IH lo hi p Hl Hlo Hhi), orb_false_r. apply not_true_iff_false. intros H.
  apply existsb_exists in H as (q & Hq & Hp). apply andb_prop in Hp as [P1 P2]. apply Z.leb_le in P1, P2. unfold page_size in P2.
  unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs. unfold bv_modulus in Ra, Rs.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Ra, Rs.
  unfold iv_subtract in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hq]. apply Z.ltb_lt in El.
    destruct Hq as [<-|[]]. cbn [fst snd] in P1, P2. rewrite ?fg_lit in P1 by lia. rewrite ?fg_lit in P2 by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hq]. apply Z.ltb_lt in Er.
    destruct Hq as [<-|[]]. cbn [fst snd] in P1, P2. rewrite ?fg_lit in P1 by lia. rewrite ?fg_lit in P2 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition fixnew_piece (L : sst) : lin :=
  match srl_lin (s_facts L) 3 (rget (s_regs L) (rkey a0r)) with Some pb => laddc pb SH_OFF | None => lc0 end.

Definition fixnew_ok (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (j : nat) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in
  match arg L 3, srl_lin fs 3 a, arg L 1 with
  | Some flags, Some pb, Some len =>
      (fixkeep_ok LIMIT res L M n false j GE && Z.eqb n (page_round_up_Z len) && Z.ltb 0 len && negb (mmap_noreserve_b (Z_to_bv 64 flags)) &&
       (let ar := irange fs a in let pr := irange fs (laddc pb SH_OFF) in      (* [comment removed for export] *)
        forallb (fun R => (rgs_sepA fs a ar n R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a n R ||| sep_res_b res R) &&&
                          (rgs_sepA fs (laddc pb SH_OFF) pr (n / 8) R ||| sep_pc_b fs (sm_maps M) j (sm_sp M) R ||| sep_pres_b res R))%bool (s_rgs L)) &&
       Z.leb (fact_hi fs (laddc a (- SH_HI)) (snd (irange fs (laddc a (- SH_HI))))) (two64 + SH_LO - n - SH_HI) && Z.leb 4096 (fst (irange fs a)) &&
       Z.leb (snd (irange fs a) + n) TOPW && shadow_ok M && zr_ok M && lwf (s_next L) pb &&
       Z.leb (eager_sum fs (set_kind j GE (sm_maps M)) + allow_bound ((laddc pb SH_OFF, n / 8) :: sm_allow M)) LIMIT)%bool
  | _, _, _ => false
  end.

Section FixNew.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved segs).
Hypothesis Hreswf : ivs_wf (segments_reserved segs).

(* [comment removed for export] *)
#[using="Hsegb Hoff Hrespos Hreswf"] Theorem den_fixnew_g : forall E L M ms model T n j (pcf : bool) (mem0' : word -> option byte),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  fixnew_ok LIMIT (segments_reserved segs) L M n j = true ->
  (forall w : word, ~ (uE E (rget (s_regs L) (rkey a0r)) <= bv_unsigned w < uE E (rget (s_regs L) (rkey a0r)) + n) -> mem0' w = mem0 w) ->
  (forall w, own_pt E M w -> uE E (rget (s_regs L) (rkey a0r)) <= bv_unsigned (Z_to_bv 64 w) < uE E (rget (s_regs L) (rkey a0r)) + n ->
     mem0' (Z_to_bv 64 w) = Some (Z_to_bv 8 0)) ->
  (pcf = true -> own_avoid E M (uE E (rget (s_regs L) (rkey a0r)) / 8 + SH_OFF) (uE E (rget (s_regs L) (rkey a0r)) / 8 + SH_OFF + n / 8)) ->
  (forall ms' model', DEN segs LIMIT model0 mem0' E
        (add_post (fix_post L (rget (s_regs L) (rkey a0r))) (rget (s_regs L) (rkey a0r)) n (if pcf then Some (fixnew_piece L) else None))
        (add_M (fix_M M j GE) n (if pcf then Some (fixnew_piece L) else None)) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T n j pcf mem0' Hd Hokn Hm0o Hm0i Hpav0 Hk.
  unfold fixnew_ok in Hokn. unfold fixnew_piece in Hk. set (a := rget (s_regs L) (rkey a0r)) in *.
  destruct (arg L 3) as [flags0|] eqn:H30; [|discriminate]. destruct (srl_lin (s_facts L) 3 a) as [pb|] eqn:Hpb; [|discriminate].
  destruct (arg L 1) as [len|] eqn:H1; [|discriminate].
  apply andb_prop in Hokn as [Hokn Hbudn]. apply Z.leb_le in Hbudn. apply andb_prop in Hokn as [Hokn Hwpb].
  apply andb_prop in Hokn as [Hokn Hzrok]. apply andb_prop in Hokn as [Hokn Hshok]. apply andb_prop in Hokn as [Hokn Hatop].
  apply Z.leb_le in Hatop. apply andb_prop in Hokn as [Hokn Halo]. apply Z.leb_le in Halo. apply andb_prop in Hokn as [Hokn Hashd].
  apply Z.leb_le in Hashd. apply andb_prop in Hokn as [Hokn Hsepc]. apply andb_prop in Hokn as [Hokn Hnnr].
  apply andb_prop in Hokn as [Hokn Hlpos]. apply andb_prop in Hokn as [Hok Hlen]. apply Z.eqb_eq in Hlen. apply Z.ltb_lt in Hlpos.
  apply negb_true_iff in Hnnr.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  unfold fixkeep_ok in Hok. fold a in Hok.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate].
  destruct (arg L 2) as [prot|] eqn:H2; [|discriminate]. rewrite H30 in Hok. rename flags0 into flags. rename H30 into H3.
  destruct (arg L 5) as [off|] eqn:H5; [|discriminate]. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate].
  apply andb_prop in Hok as [Hok Hgm]. apply negb_true_iff in Hgm.
  apply andb_prop in Hok as [Hok Hbc]. apply Z.leb_le in Hbc. apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud.
  apply andb_prop in Hok as [Hok Hwa]. apply andb_prop in Hok as [Hok Hzrc]. apply andb_prop in Hok as [Hok Halc].
  apply andb_prop in Hok as [Hok _].
  apply andb_prop in Hok as [Hok Hrgc]. apply andb_prop in Hok as [Hok Hkdc]. apply andb_prop in Hok as [Hok Hdal].
  apply andb_prop in Hok as [Hok Hdc]. apply andb_prop in Hok as [Hok Hsel].
  apply andb_prop in Hok as [Hok Hnac]. apply andb_prop in Hok as [Hok Hmod]. apply andb_prop in Hok as [Hok _].
  apply andb_prop in Hok as [Hok Hanon]. apply andb_prop in Hok as [Hc7 Hoffa]. apply Z.eqb_eq in Hc7. subst c7.
  apply negb_true_iff in Hmod, Hnac.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = lden E a) by exact (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (is_const_sound E _ len H1) as [_ Hlen64].
  assert (Hnz0 : w_is0 (Z_to_bv 64 len) = false) by (unfold w_is0, bv_eqb; apply Z.eqb_neq; rewrite fg64 by exact Hlen64; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  assert (HnZ : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = n) by (rewrite fg64 by exact Hlen64; symmetry; exact Hlen).
  assert (HnZpos : 0 < n) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : n mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5).
  pose proof Hgtop as Hgtop0. rewrite Forall_forall in Hgtop0. pose proof (Hgtop0 g Hgj) as Gt.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _ & _ & _ & HG0 & HD0 & HF0 & _).
  pose proof (gsz_bounds E (s_facts L) g HF0) as Gb. pose proof (gsz_lo_nonneg (s_facts L) g) as Gb0.
  destruct (contained_sound E (s_facts L) a n (fst (fst g)) (gsz_lo (s_facts L) g) HF0 Hdc HnZpos ltac:(unfold uE, two64 in *; lia)) as [Hlo Hhi0].
  assert (Hhi : uE E a + n <= uE E (fst (fst g)) + gsz E g) by lia.
  assert (Hal : uE E a mod 4096 = 0) by (apply (lal_ok_sound E a (fst (fst g)) Hdal Gs3 Hlo); unfold uE, two64 in *; lia).
  assert (Hrsep : forall R, In R (s_rgs L) ->
            (rgs_sepA (s_facts L) a (irange (s_facts L) a) n R || sep_app2_b (s_facts L) (sm_maps M) j (sm_sp M) a n R || sep_res_b (segments_reserved segs) R)%bool = true /\
            (rgs_sepA (s_facts L) (laddc pb SH_OFF) (irange (s_facts L) (laddc pb SH_OFF)) (n / 8) R || sep_pc_b (s_facts L) (sm_maps M) j (sm_sp M) R || sep_pres_b (segments_reserved segs) R)%bool = true).
  { intros R HR. rewrite forallb_forall in Hsepc. apply andb_prop. exact (Hsepc R HR). }
  (* [comment removed for export] *)
  pose proof (irange_sound E _ a HF0) as Ra. pose proof (irange_sound E _ (laddc a (- SH_HI)) HF0) as Rsh0.
  assert (Rsh : 0 <= bv_unsigned (lden E (laddc a (- SH_HI))) <= two64 + SH_LO - n - SH_HI).
  { pose proof (fact_hi_sound E _ (laddc a (- SH_HI)) _ HF0 (proj2 Rsh0)) as X. unfold uE in X.
    pose proof (bv_unsigned_in_range _ (lden E (laddc a (- SH_HI)))). lia. }
  assert (HuA : bv_unsigned (lden E a) = uE E a) by reflexivity.
  assert (Hpf : place_facts (lden E a) n).
  { constructor.
    - rewrite HuA. exact Hal.
    - rewrite HuA. unfold uE. lia.
    - rewrite HuA. unfold uE. lia.
    - rewrite lden_laddc in Rsh. rewrite HuA. unfold uE in *. pose proof (u_lt (lden E a)) as R64.
      rewrite Z_to_bv_unsigned in Rsh. unfold bv_wrap, bv_modulus in Rsh. change (2 ^ Z.of_N 64) with two64 in Rsh.
      destruct (Z_le_gt_dec SH_HI (bv_unsigned (lden E a))) as [Hge|Hlt]; [right; exact Hge|left].
      replace (bv_unsigned (lden E a) + - SH_HI) with ((bv_unsigned (lden E a) - SH_HI + two64) + (-1) * two64) in Rsh by lia.
      rewrite Z.mod_add in Rsh by (unfold two64; lia). rewrite Z.mod_small in Rsh by (unfold SH_HI, two64 in *; lia). lia. }
  assert (Hnsh : uE E a + n <= SH_LO \/ SH_HI <= uE E a) by (destruct Hpf as [_ _ _ Hs]; rewrite HuA in Hs; exact Hs).
  assert (HsepA : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n)).
  { intros R HR w Hw Hin. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (HRs & HRw & _).
    destruct (Hrsep R HR) as [Hc _]. apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|].
    - exact (rgs_sepA_sound E (s_facts L) a n R HF0 ltac:(lia) ltac:(unfold uE in *; lia) HRw Hc w Hw Hin).
    - exact (sep_app2_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok)
               j g a n R Hj Hgm Hlo Hhi ltac:(unfold uE, two64 in *; lia) HRs HRw Hc w Hw Hin).
    - rewrite <- Hres in Hc. exact (sep_res_sound E (sm_maps M) model _ Hmaps Hgsh Hmres j g a n R Hj Hgm Hlo Hhi Hc w Hw Hin). }
  assert (Hov : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
      false = false /\ rg_kind R = RZ /\
      (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0))).
  { intros R HR w Hw Hin. exfalso. exact (HsepA R HR w Hw Hin). }
  assert (Hallow : mmap_noreserve_b (Z_to_bv 64 flags) = true -> forall w, uE E a <= w < uE E a + n ->
                     page_allowedb (allowA E M) (page_base (Z_to_bv 64 w)) = true).
  { intros Hnr. rewrite Hnr in Hnnr. discriminate. }
  assert (Hnazr : false = true -> forall w, uE E a <= w < uE E a + n -> in_zr (sm_zr M) w = false) by discriminate.
  assert (Hkd : GE = GE \/ (GE = snd g /\ (false = true \/ mmap_noreserve_b (Z_to_bv 64 flags) = true))) by (left; reflexivity).
  assert (Hkdn : GE <> GN) by discriminate.
  assert (Hm0i' : forall w, own_pt E M w -> uE E a <= bv_unsigned (Z_to_bv 64 w) < uE E a + n ->
     mem0' (Z_to_bv 64 w) = fresh_mem false (ms_mem ms) (lden E a) (Z_to_bv 64 n) (Z_to_bv 64 w)).
  { intros w Hop Hr. rewrite (Hm0i w Hop Hr). symmetry. apply fresh_mem_in.
    rewrite (fg64 n) by (unfold uE, two64 in *; lia). exact Hr. }
  pose proof (fix_keep_den segs LIMIT model0 mem0 Hsegb E L M ms model a n false (Z_to_bv 64 flags) j g GE mem0' Hd Hwa Hj Hgm
                ltac:(lia) ltac:(lia) HnZpos HnZal Hal Hkd Hkdn Hov Hallow Hnazr Hbud Hm0o Hm0i') as HD'.
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  assert (Htop : uE E a + n <= alloc_top (m_vmmaps model)) by lia.
  assert (Hgate : fixed_gate model (lden E a) (Z_to_bv 64 len)).
  { unfold fixed_gate, page_size. rewrite HuA, HnZ. repeat split; lia. }
  assert (HnZw : bv_unsigned (Z_to_bv 64 n) = n) by (apply fg64; pose proof (u_lt (lden E a)); unfold uE, two64 in *; lia).
  assert (Hcm : forall x, uE E a <= x < uE E a + n -> covered (vm_maps (m_vmmaps model)) x = true).
  { intros x Hx. rewrite Hmaps. apply (covered_In _ (gden E g)); [exact (lden_maps_in E _ _ g Hgj Hgm)|]. unfold gden. rewrite in_iv_word.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold gsz, uE in *; lia. }
  assert (Hctn : (region_free (vm_reserved (m_vmmaps model)) (lden E a) (Z_to_bv 64 n)
                  && map_contains (vm_maps (m_vmmaps model)) (lden E a) (Z_to_bv 64 n))%bool = true).
  { apply andb_true_intro. split.
    - rewrite Hres. apply region_free_of_pts; [exact Hreswf | exact Hrespos | | rewrite HnZw; exact HnZpos].
      intros x Hx. rewrite HnZw, HuA in Hx. rewrite <- Hres. exact (Hmres x (Hcm x Hx)).
    - rewrite Hmaps. apply (map_contains_intro _ _ _ (fst (gden E g)) (snd (gden E g))); [rewrite <- surjective_pairing; exact (lden_maps_in E _ _ g Hgj Hgm) | |].
      + unfold gden. cbn [fst]. unfold uE in *. lia.
      + unfold gden. cbn [fst snd]. rewrite HnZw, HuA. unfold gsz, uE in *. lia. }
  rewrite <- HnZ in Hctn.
  (* [comment removed for export] *)
  pose proof (srl_lin_sound E _ 3 a pb HF0 ltac:(lia) Hpb) as Hpbv.
  assert (HPu : uE E (laddc pb SH_OFF) = uE E a / 8 + SH_OFF).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned, Hpbv. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. pose proof (u_lt (lden E a)).
    assert (bv_unsigned (lden E a) / 8 <= bv_unsigned (lden E a)) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= bv_unsigned (lden E a) / 8) by (apply Z.div_pos; lia). unfold SH_OFF, two64 in *. lia. }
  assert (Ha47 : uE E a + n <= 0x800000000000) by (unfold uE in *; lia).
  assert (Ha8 : uE E a mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (512 * q). lia. }
  set (ms' := advance_past_svc (apply_effect (svc_set ms) (fresh_eff false (lden E a) (Z_to_bv 64 n)))) in *.
  set (model' := fixed_next false (Z_to_bv 64 flags) (lden E a) (Z_to_bv 64 n) model) in *.
  assert (Hvm' : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model)) by (unfold model'; rewrite fx_vmmaps; reflexivity).
  assert (Hlz' : m_vm_lazy model' = maps_subtract (m_vm_lazy model) (uE E a) (uE E a + n)).
  { unfold model'. rewrite fx_lazy, Hnnr. cbn [app]. rewrite HnZw. reflexivity. }
  assert (HD2 : DEN segs LIMIT model0 mem0' E (add_post (fix_post L a) a n (if pcf then Some (laddc pb SH_OFF) else None))
                  (add_M (fix_M M j GE) n (if pcf then Some (laddc pb SH_OFF) else None)) ms' model').
  { apply (den_add segs LIMIT model0 mem0' E (fix_post L a) (fix_M M j GE) ms' model' a n (if pcf then Some (laddc pb SH_OFF) else None) HD' Hwa HnZpos HnZal Hal Ha47).
    - intros x Hx. rewrite Hvm'. split; [exact (Hcm x Hx)|]. unfold in_shadow, SH_LO, SH_HI.
      destruct Hpf as [_ _ _ Hsh]. rewrite HuA in Hsh. unfold SH_LO, SH_HI in Hsh.
      apply andb_false_iff. destruct Hsh as [Hs|Hs]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
    - intros x Hx. split.
      + unfold ms'. rewrite fresh_full_mem. apply fresh_mem_in. rewrite HuA, HnZw, fg64 by (unfold two64; lia). lia.
      + unfold Hof, mkH. rewrite Hlz'. rewrite (page_in_ms_inside _ (uE E a) (uE E a + n)); [reflexivity | exact (proj2 Hivwf) | |].
        * pose proof (pb_bounds (Z_to_bv 64 x)) as (P1 & P2). rewrite fg64' in P1 by (unfold two64; lia).
          pose proof (Z.div_mod (bv_unsigned (page_base (Z_to_bv 64 x))) 4096 ltac:(lia)). pose proof (Z.div_mod (uE E a) 4096 ltac:(lia)).
          assert (bv_unsigned (page_base (Z_to_bv 64 x)) / 4096 >= uE E a / 4096) by lia. lia.
        * pose proof (pb_bounds (Z_to_bv 64 x)) as (P1 & P2). rewrite fg64' in P1 by (unfold two64; lia).
          pose proof (Z.div_mod (bv_unsigned (page_base (Z_to_bv 64 x))) 4096 ltac:(lia)). pose proof (Z.div_mod (uE E a + n) 4096 ltac:(lia)).
          assert ((uE E a + n) mod 4096 = 0) by (rewrite Z.add_mod, Hal, HnZal by lia; reflexivity).
          assert (bv_unsigned (page_base (Z_to_bv 64 x)) / 4096 < (uE E a + n) / 4096) by lia. lia.
    - exact HsepA.
    - intros P HP. destruct pcf; [|discriminate]. injection HP as <-. split; [apply lwf_laddc; exact Hwpb|]. split; [exact HPu|].
      assert (Hn8 : (uE E a + n) / 8 = uE E a / 8 + n / 8).
      { apply Z.mod_divide in Ha8; [|lia]. destruct Ha8 as [q Hq]. apply Z.mod_divide in HnZal; [|lia]. destruct HnZal as [r Hr].
        rewrite Hq, Hr. replace (q * 8 + r * 4096) with ((q + r * 512) * 8) by lia. rewrite !Z.div_mul by lia.
        replace (r * 4096) with ((r * 512) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      split.
      + intros y Hy. rewrite HPu in Hy. rewrite Hvm', Hmaps.
        destruct (piece_pts E (blob_of model0) M (lden E a) n y Hshok Hpf HnZpos HnZal ltac:(rewrite HuA; lia)) as (Q1 & Q2 & Q3).
        split; [exact Q1|]. split; [exact (Q2 Hzrok) | exact Q3].
      + intros R HR w Hw. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (HRs & HRw & _).
        assert (Hp47 : uE E (laddc pb SH_OFF) + n / 8 <= 0x800000000000).
        { rewrite HPu. assert (uE E a / 8 <= uE E a) by (apply Z.div_le_upper_bound; lia).
          assert (n / 8 <= n) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF. lia. }
        destruct (Hrsep R HR) as [_ Hc]. apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|].
        * exact (rgs_sepA_sound E (s_facts L) (laddc pb SH_OFF) (n / 8) R HF0 ltac:(apply Z.div_pos; lia) Hp47 HRw Hc w Hw).
        * rewrite HPu. intros Hin.
          destruct (piece_pts E (blob_of model0) M (lden E a) n (uE E a / 8 + SH_OFF) Hshok Hpf HnZpos HnZal ltac:(rewrite HuA; lia)) as (Q1 & _).
          destruct (piece_pts E (blob_of model0) M (lden E a) n (uE E a / 8 + SH_OFF + n / 8 - 1) Hshok Hpf HnZpos HnZal) as (Q1' & _).
          { rewrite HuA. assert (0 < n / 8) by (apply Z.div_str_pos; pose proof (Z.mod_pos_bound n 4096 ltac:(lia)); lia). lia. }
          unfold in_shadow in Q1, Q1'. apply andb_prop in Q1 as [Q1a _]. apply andb_prop in Q1' as [_ Q1b].
          apply Z.leb_le in Q1a. apply Z.ltb_lt in Q1b.
          exact (sep_pc_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok)
                   j g a n R Hj Hgm Hlo Hhi Ha8 ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in HnZal; [|lia]; destruct HnZal as [q Hq]; exists (512 * q); lia)
                   HnZpos Q1a ltac:(lia) HRs HRw Hc w Hw Hin).
        * rewrite HPu. rewrite <- Hres in Hc.
          exact (sep_pres_sound E (sm_maps M) model _ Hmaps Hgsh Hmres j g a n R Hj Hgm Hlo Hhi Ha8
                   ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in HnZal; [|lia]; destruct HnZal as [q Hq]; exists (512 * q); lia) Hc w Hw).
    - destruct pcf; [exact Hbudn|]. cbn [add_M fix_M sm_allow sm_maps app fix_post s_facts]. unfold allow_bound in *. cbn [fold_right snd] in Hbudn.
      assert (0 <= n / 8) by (apply Z.div_pos; lia). lia.
    - intros P HP. destruct pcf; [|discriminate]. injection HP as <-. rewrite HPu. exact (Hpav0 eq_refl).
    - intros P HP y Hy. destruct pcf; [|discriminate]. injection HP as <-. rewrite HPu in Hy.
      assert (Hn8' : (uE E a + n) / 8 = uE E a / 8 + n / 8).
      { apply Z.mod_divide in Ha8; [|lia]. destruct Ha8 as [q Hq]. pose proof HnZal as HnZal'. apply Z.mod_divide in HnZal'; [|lia]. destruct HnZal' as [r Hr].
        rewrite Hq, Hr. replace (q * 8 + r * 4096) with ((q + r * 512) * 8) by lia. rewrite !Z.div_mul by lia.
        replace (r * 4096) with ((r * 512) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      exact (blob_sh_grant E M model _ j g (uE E a) n y Hmaps Hpd Hblob Hj Hgm Hlo Hhi ltac:(lia)). }
  apply andb_prop in Hsel as [Hsel1 Hsel2]. apply negb_true_iff in Hsel1.
  assert (Hbr := branch_fixed_rw_contained segs ms1 (ms_reg ms 17) model Hno).
  rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr, Hctn.
  specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hsel1 Hsel2 Hgate Hctn).
  eapply rzc_silent1; [|exact (Hk _ _ HD2)].
  apply (node_mmap_fixed_rw_contained segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n) (Z_to_bv 64 flags) Hh Hsvc Hno
           ltac:(rewrite HuA; lia) Hbr).
  (* [comment removed for export] *)
  assert (Hmw : model_ivs_wf model).
  { split; [rewrite Hmaps; exact (ivs_wf_lden E model _ _ Hgsh (proj1 Hblob))|]. split; [exact (proj1 Hivwf)|]. split; [exact (proj2 Hivwf) | exact (proj1 Hspok)]. }
  apply mmap_fixed_rw_budget_ok_commit_intro; [exact Hnnr | exact Hmw|]. rewrite Hlim.
  assert (Hov' : overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + bv_unsigned (Z_to_bv 64 n))
                 <= Z.of_nat (length (vm_maps (m_vmmaps model))) * n).
  { rewrite HnZw. clear -HnZpos. induction (vm_maps (m_vmmaps model)) as [|g0 r IH]; [unfold overlap_sum; cbn; lia|].
    cbn [length]. rewrite overlap_sum_cons. pose proof (iv_count_in_rng_le g0 (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + n) ltac:(lia)).
    lia. }
  destruct (ledger_lden_bounds E model (s_facts L) _ _ HF0 Hgsh (proj1 Hblob) (proj2 (proj2 Hblob))) as [_ Hln]. rewrite <- Hmaps in Hln.
  pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn.
  assert (Hvb : vm_backing_used model <= eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M))
    by exact (den_backing_le segs LIMIT model0 mem0 E L M ms model (s_facts L) Hd HF0).
  assert (Z.of_nat (length (vm_maps (m_vmmaps model))) * n <= (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.
(* [comment removed for export] *)
#[using="Hsegb Hoff Hrespos Hreswf"] Theorem den_fixnew : forall E L M ms model T n j,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] ->
  fixnew_ok LIMIT (segments_reserved segs) L M n j = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E
        (add_post (fix_post L (rget (s_regs L) (rkey a0r))) (rget (s_regs L) (rkey a0r)) n (Some (fixnew_piece L)))
        (add_M (fix_M M j GE) n (Some (fixnew_piece L))) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T n j Hd Hon Hokn Hk.
  apply (den_fixnew_g E L M ms model T n j true mem0 Hd Hokn (fun w _ => eq_refl)
           (fun w Hop _ => False_ind _ (own_pt_nil E M w Hon Hop)) (fun _ => own_avoid_nil E M _ _ Hon) Hk).
Qed.
End FixNew.
