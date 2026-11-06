(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxRunPost.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record bsite : Type := BS { bs_pc : Z; bs_rd : reg; bs_ra : reg; bs_rm : reg; bs_k : Z; bs_j : Z }.
Definition bsite_ok (segs : list Segment) (s : bsite) : Prop :=
  bs_rd s <> 0%bv /\ 0 < bs_k s < bs_j s /\ bs_j s < 64 /\ 0 <= bs_pc s /\ bs_pc s + 4 < two64 /\
  qins segs (bs_pc s) 0 (Op ALU_AND (bs_rd s) (bs_ra s) (bs_rm s)).

Definition band_res (s : bsite) (S : sst) : option lin :=
  let fs := s_facts S in
  match s_resv S, is_const (rget (s_regs S) (rkey (bs_rm s))) with
  | RNone, Some m =>
      let a := rget (s_regs S) (rkey (bs_ra s)) in
      if (Z.eqb (s_pc S) (bs_pc s) && Z.eqb m (2 ^ bs_j s - 2 ^ bs_k s) && Z.ltb (snd (irange fs a)) (2 ^ bs_j s))%bool then
        match and_lin fs (two64 - 2 ^ bs_k s) a with
        | Some l => if lwf (s_next S) l then Some l else None
        | None => None
        end
      else None
  | _, _ => None
  end.
Definition band_post (s : bsite) (S : sst) : option sst :=
  match band_res s S with Some l => Some (run_post S (bs_pc s + 4) [(bs_rd s, l)] []) | None => None end.

(* [comment removed for export] *)
Lemma land_band : forall a k j, 0 < k < j -> j < 64 -> 0 <= a < 2 ^ j -> Z.land a (2 ^ j - 2 ^ k) = Z.land a (two64 - 2 ^ k).
Proof.
  intros a k j Hk Hj Ha.
  assert (E1 : 2 ^ j - 2 ^ k = Z.shiftl (Z.ones (j - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. rewrite Z.mul_pred_l. rewrite <- Z.pow_add_r by lia.
    replace (j - k + k) with j by lia. lia. }
  assert (E2 : two64 - 2 ^ k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. rewrite Z.mul_pred_l. rewrite <- Z.pow_add_r by lia.
    replace (64 - k + k) with 64 by lia. unfold two64. lia. }
  rewrite E1, E2. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i k) as [Hik|Hik].
  - rewrite !Z.shiftl_spec_low by lia. reflexivity.
  - rewrite !Z.shiftl_spec by lia.
    destruct (Z_lt_dec i j) as [Hij|Hij].
    + rewrite !Z.ones_spec_low by lia. reflexivity.
    + assert (Hb : Z.testbit a i = false).
      { destruct (Z.eq_dec a 0) as [->|Hne]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
        assert (Z.log2 a < j) by (apply Z.log2_lt_pow2; lia). lia. }
      rewrite Hb. reflexivity.
Qed.

Section Node.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_band : forall s S S' M E ms model T,
  bsite_ok segs s -> band_post s S = Some S' -> DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' S' M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros s S S' M E ms model T Hs Hp Hd Hk.
  destruct s as [pc0 rd ra rm k j]. destruct Hs as (Hrd & Hkj & Hj & Hpc0 & Hpc4 & Hins). cbn [bs_pc bs_rd bs_ra bs_rm bs_k bs_j] in *.
  unfold band_post in Hp. destruct (band_res (BS pc0 rd ra rm k j) S) as [l|] eqn:Hr; [|discriminate]. injection Hp as <-.
  unfold band_res in Hr. cbn [bs_pc bs_rd bs_ra bs_rm bs_k bs_j] in Hr.
  set (fs := s_facts S) in *. set (a := rget (s_regs S) (rkey ra)) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (is_const (rget (s_regs S) (rkey rm))) as [m|] eqn:Hm; [|discriminate].
  destruct (Z.eqb (s_pc S) pc0 && Z.eqb m (2 ^ j - 2 ^ k) && Z.ltb (snd (irange fs a)) (2 ^ j))%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hlt]. apply andb_prop in Hc as [Hpc Hmm]. apply Z.eqb_eq in Hpc, Hmm. apply Z.ltb_lt in Hlt.
  destruct (and_lin fs (two64 - 2 ^ k) a) as [l0|] eqn:Hal; [|discriminate].
  destruct (lwf (s_next S) l0) eqn:Hwl; [|discriminate]. injection Hr as <-.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpcv & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpcv, Hsvc, Hrsv, HR.
  destruct Hins as (w0 & F0 & E0 & D0).
  set (A := lden E a). set (Mw := Z_to_bv 64 m).
  assert (HA : getr (ms_regs ms) ra = A) by exact (HR ra).
  assert (HM : getr (ms_regs ms) rm = Mw) by (rewrite (HR rm); exact (proj1 (is_const_sound E _ m Hm))).
  pose proof (irange_sound E fs a HF) as Ra. fold A in Ra.
  pose proof (bv_unsigned_in_range _ A) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  assert (H2k : 0 < 2 ^ k < 2 ^ j) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  assert (H2j : 2 ^ j < two64) by (change two64 with (2 ^ 64); apply Z.pow_lt_mono_r; lia).
  assert (Hm64 : 0 <= m < two64) by lia.
  set (regs' := regupd (ms_regs ms) rd (v_and A Mw)).
  assert (Hval : v_and A Mw = lden E l0).
  { rewrite (and_lin_sound E fs (two64 - 2 ^ k) a l0 HF ltac:(lia) Hal). fold A. apply bv_eq. rewrite bv_and_unsigned.
    assert (Hland : 0 <= Z.land (bv_unsigned A) m < two64).
    { split; [apply Z.land_nonneg; lia|]. destruct (Z.eq_dec (Z.land (bv_unsigned A) m) 0) as [->|Hne]; [unfold two64; lia|].
      assert (Hpos : 0 < Z.land (bv_unsigned A) m) by (pose proof (Z.land_nonneg (bv_unsigned A) m); lia).
      change two64 with (2 ^ 64). apply Z.log2_lt_pow2; [exact Hpos|].
      pose proof (Z.log2_land (bv_unsigned A) m ltac:(lia) ltac:(lia)) as Hl2.
      assert (Z.log2 m < 64) by (apply Z.log2_lt_pow2; [lia | change (2 ^ 64) with two64; lia]). lia. }
    unfold v_and, Mw. rewrite (u_small64 m) by exact Hm64. rewrite (u_small64 (two64 - 2 ^ k)) by (unfold two64 in *; lia).
    rewrite (u_small64 (Z.land (bv_unsigned A) m)) by (unfold two64 in *; lia). rewrite Hmm. apply land_band; lia. }
  assert (Hst : RiscvSemantics.step segs (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) (mrestrict H (ms_mem ms)) (ms_rom ms)) =
                MachineOk (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qpc pc0 1) (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { rewrite (step_and segs (ms_regs ms) (qpc pc0 0) (mrestrict H (ms_mem ms)) (ms_rom ms) w0 rd ra rm F0 E0 D0).
    rewrite (PropExec.bv_eqb_neq rd 0%bv Hrd). rewrite qpc_succ, HA, HM. reflexivity. }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpcv. subst sv rv.
    cbn [ms_pc_val] in Hpcv. rewrite Hpc in Hpcv. subst pcv.
    unfold restrict, mkst, qpc. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pc0 + 4 * 0) with pc0 by lia. reflexivity. }
  apply (den_run_post segs cfg LIMIT model0 mem0 Hwx E S M ms model T regs' (pc0 + 4) [(rd, l0)] [] Hd Hrv).
  - fold H. rewrite Hmsr. replace (Z_to_bv 64 (pc0 + 4)) with (qpc pc0 1) by (unfold qpc; f_equal; lia).
    eapply FxStep.ist_step; [reflexivity | exact Hst | apply FxStep.ist_refl].
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [exact Hrd|]. split; [exact Hwl|].
    unfold regs'. rewrite getr_same by exact Hrd. exact Hval.
  - apply Forall_nil.
  - intros r Hs _. cbn [existsb fst] in Hs. apply orb_false_elim in Hs as [Hs _].
    unfold regs'. rewrite getr_other; [reflexivity|]. intros Hc. subst r. rewrite bv_eqb_refl in Hs. discriminate.
  - exact Hk.
Qed.
End Node.
(* [comment removed for export] *)
