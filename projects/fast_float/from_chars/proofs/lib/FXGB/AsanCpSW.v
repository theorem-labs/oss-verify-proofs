(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv FxChFam FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxRunPost FxRunPostM FxSNodes AsanMBase AsanMcpy AsanCpS.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanMBase OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanMcpy OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rsz_top : Z := 18446744073709551616.
(* [comment removed for export] *)
Definition run_post_win (S : sst) (pc' : Z) (sets : list (reg * lin)) (havs : list reg) (j0 : nat) (klo : Z) : sst :=
  match nth_error (s_rgs S) j0 with
  | Some R0 => SST pc' (hav_regs (set_regs (s_regs S) sets) havs (s_next S))
                   (upd_nth (s_rgs S) j0 (RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) klo rsz_top)))
                   (s_facts S) (pos_add (s_next S) (length havs)) (s_resv S)
  | None => run_post S pc' sets havs
  end.

Section M.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_run_post_win_m : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg)
    (j0 : nat) (R0 : region) (klo : Z) (mem' : word -> option byte),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  nth_error (s_rgs S) j0 = Some R0 -> rk_wz (rg_kind R0) = true ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)) ->
  0 <= klo ->
  (forall w : word, ~ (uE E (rg_base R0) + klo <= bv_unsigned w < uE E (rg_base R0) + rsz E R0) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w) ->
  (forall i, 0 <= i < rsz E R0 -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None /\ wview segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post_win S pc' sets havs j0 klo) M ms' model' ->
     (forall w, Hof E' M model' w = false -> ms_mem ms' w = mem' w) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs j0 R0 klo mem' Hd Hrv Hj0 Hk0 Hst Hklo Hfrw Hwr Hsets Hnz Ho Hk.
  assert (Hfr : forall w : word, ~ (uE E (rg_base R0) <= bv_unsigned w < uE E (rg_base R0) + rsz E R0) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w)
    by (intros w Hw; apply Hfrw; lia).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (R0' := RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) klo (rsz_top))).
  assert (Hpw : run_post_win S pc' sets havs j0 klo = SST pc' (hav_regs (set_regs (s_regs S) sets) havs n) (upd_nth (s_rgs S) j0 R0')
                   (s_facts S) (pos_add n (length havs)) (s_resv S)) by (unfold run_post_win; rewrite Hj0; reflexivity).
  set (msr' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)).
  assert (Hpost : sden segs E1 (run_post_win S pc' sets havs j0 klo) msr').
  { rewrite Hpw. intros E' Ha'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' (pos_add_le (length havs) n) Ha')).
    destruct (Hsd E' HaE) as (Hpc' & Hsvc' & Hrsv' & HR' & HG' & HD' & HF' & Hfrm').
    cbn [restrict ms_regs ms_mem ms_fcsr ms_resv] in HR', HG', Hfrm', Hrsv'.
    assert (HbE : lden E' (rg_base R0) = lden E (rg_base R0)).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 _].
      exact (lden_agree_wf n E E' _ B1 HaE). }
    assert (HsE : rsz E' R0 = rsz E R0).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [_ B2].
      unfold rsz. rewrite (lden_agree_wf n E E' _ B2 HaE). reflexivity. }
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv msr' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|]. split.
    - apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
      + apply regs_ok_hav'; [| exact Hnz |].
        * apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
          destruct (Hsets p Hp) as (Hp0 & Hpw' & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw' HaE).
        * intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. cbn [s_next]. apply pos_add_lt. exact Hi.
      + intros r. rewrite upd_havs_get, upd_sets_get.
        destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
        destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
        symmetry. exact (Ho r Es Eh).
    - split; [|split; [|split; [exact HF' | exact Hfrm']]].
      + (* [comment removed for export] *)
        apply Forall_nth'. intros j R HRj. rewrite Forall_nth' in HG'.
        destruct (Nat.eq_dec j j0) as [->|Hne].
        * rewrite (nth_upd_same (s_rgs S) j0 R0' R0 Hj0) in HRj. injection HRj as <-.
          destruct (HG' j0 R0 Hj0) as (Hsz & Hflat & _ & _).
          assert (Hrsz : rsz E' R0' = rsz E R0) by (unfold R0', rsz; cbn [rg_size]; unfold rsz in HsE; exact HsE).
          assert (Hbase : lden E' (rg_base R0') = lden E (rg_base R0)) by (unfold R0'; cbn [rg_base]; exact HbE).
          unfold rg_ok. rewrite Hrsz, Hbase. rewrite HbE, HsE in *. fold (uE E (rg_base R0)) in *. cbn [rg_kind rg_cont R0'].
          split; [exact Hsz|]. split; [exact Hflat|]. split.
          -- intros i Hi. exact (Hwr i Hi).
          -- intros p v Hp. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
             destruct (tget p (rg_cont R0)) as [v0|] eqn:Hp0; [|discriminate]. cbv beta in Hp.
             destruct (negb (Z.leb klo (Z.pos p - 1) && Z.ltb (Z.pos p - 1) rsz_top)) eqn:Hkeep; [|discriminate]. injection Hp as <-.
             destruct (HG' j0 R0 Hj0) as (_ & _ & _ & Hc). rewrite HbE, HsE in Hc. fold (uE E (rg_base R0)) in Hc.
             destruct (Hc p v0 Hp0) as [Hlt Hrd]. split; [exact Hlt|].
             assert (Hbelow : Z.pos p - 1 < klo).
             { apply negb_true_iff in Hkeep. apply andb_false_iff in Hkeep as [X|X]; [apply Z.leb_gt in X; exact X|].
               apply Z.ltb_ge in X. unfold rsz_top in X. pose proof (bv_unsigned_in_range _ (lden E (rg_size R0))) as RR. unfold rsz in *.
               unfold bv_modulus in RR. change (2 ^ Z.of_N 64) with 18446744073709551616 in RR. lia. }
             pose proof (Pos2Z.is_pos p) as Hpp.
             assert (Hflat' : uE E (rg_base R0) + rsz E R0 <= two64) by exact Hflat.
             unfold rd1 in *. rewrite Hfrw; [exact Hrd|].
             pose proof (uE_range E (rg_base R0)) as UB.
             rewrite u_small64 by (unfold two64 in *; lia). lia.
        * rewrite (nth_upd_other (s_rgs S) j0 j R0' ltac:(lia)) in HRj.
          apply (rg_ok_frame segs E' (mrestrict H (ms_mem ms)) mem' R (HG' j R HRj)).
          intros x Hx. apply Hfr.
          pose proof (rgs_disj_nth E' (s_rgs S) j j0 R R0 HD' Hne HRj Hj0) as Hdis. unfold rg_disj in Hdis.
          rewrite HbE, HsE in Hdis. fold (uE E (rg_base R0)) in Hdis. unfold uE in *. lia.
      + apply (rgs_disj_upd E' (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl HD'). }
  apply (den_isteps_m segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (run_post_win S pc' sets havs j0 klo) msr' E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - rewrite Hpw. unfold S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y Hy. rewrite HH1. unfold msr', mkst. cbn [ms_mem]. apply Hfr.
    unfold outside in Hy. rewrite Forall_forall in Hy. specialize (Hy R0 (nth_error_In _ _ Hj0)).
    cbn [S1 bump s_rgs] in Hy.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 B2].
    assert (HbE1 : lden E1 (rg_base R0) = lden E (rg_base R0)) by exact (lden_agree_wf n E E1 _ B1 Ha1).
    assert (HsE1 : rsz E1 R0 = rsz E R0) by (unfold rsz; rewrite (lden_agree_wf n E E1 _ B2 Ha1); reflexivity).
    rewrite HbE1, HsE1 in Hy. unfold uE. lia.
  - rewrite Hpw. cbn [s_rgs S1 bump]. exact (shape_upd (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl).
  - intros E2 ms2 model2 HD2 Ha2 Hm2. apply (Hk E2 ms2 model2); [| exact HD2 | exact Hm2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End M.

Definition cpsw_post (S : sst) : sst :=
  match rg_is S 1, find_win rk_wz (s_facts S) (s_rgs S) (rget (s_regs S) (rkey (xr 10))) (rget (s_regs S) (rkey (xr 12))) O with
  | Some r, Some j0 =>
      match nth_error (s_rgs S) j0 with
      | Some Rd => run_post_win S r [] CPS_HAVS j0 (Z.max 0 (fst (irange (s_facts S) (lsub (rget (s_regs S) (rkey (xr 10))) (rg_base Rd)))))
      | None => S
      end
  | _, _ => S
  end.

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Hwx"] Theorem den_cpsw : forall S M E ms model T,
  cps_chk img S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (cpsw_post S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M E ms model T Hck Hd Hk.
  unfold cps_chk in Hck. unfold cpsw_post in Hk.
  set (fs := s_facts S) in *. set (d := rget (s_regs S) (rkey (xr 10))) in *. set (s := rget (s_regs S) (rkey (xr 11))) in *.
  set (nl := rget (s_regs S) (rkey (xr 12))) in *.
  destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (find_win rk_wz fs (s_rgs S) d nl O) as [j0|] eqn:Hf0; [|discriminate].
  destruct (find_win rk_rd fs (s_rgs S) s nl O) as [j1|] eqn:Hf1; [|discriminate].
  apply andb_prop in Hck as [Hck Hnl]. apply andb_prop in Hck as [Hck Hj01]. apply andb_prop in Hck as [Hpc0 Hr2].
  apply Z.eqb_eq in Hpc0. apply Z.eqb_eq in Hr2. apply Z.leb_le in Hnl. apply negb_true_iff, Nat.eqb_neq in Hj01.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  destruct (find_win_spec _ _ _ _ _ _ _ Hf0) as (Rd & Hj0 & _ & Hk0 & Hw0). rewrite Nat.sub_0_r in Hj0.
  destruct (find_win_spec _ _ _ _ _ _ _ Hf1) as (Rs & Hj1 & _ & Hk1 & Hw1). rewrite Nat.sub_0_r in Hj1.
  pose proof (irange_sound E fs nl HF) as Rn. fold (uE E nl) in Rn.
  assert (HN : uE E nl <= 2 ^ 40) by lia.
  destruct (win_ok_sound E fs d nl Rd HF Hw0 HN) as (W1 & W2 & W3 & W4 & W5).
  destruct (win_ok_sound E fs s nl Rs HF Hw1 HN) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uE_range E nl) as UN. pose proof (uE_range E d) as UD. pose proof (uE_range E s) as US.
  set (D := uE E d) in *. set (Sx := uE E s) in *. set (N := uE E nl) in *.
  set (AD := uE E (rg_base Rd)) in *. set (AS := uE E (rg_base Rs)) in *.
  rewrite Forall_nth' in HG.
  pose proof (HG j0 Rd Hj0) as HRd. pose proof (HG j1 Rs Hj1) as HRs.
  destruct HRd as (Hdsz & Hdfl & Hdpts & _). destruct HRs as (Hssz & Hsfl & Hspts & _).
  fold AD in Hdpts. fold AS in Hspts.
  (* [comment removed for export] *)
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). fold d. unfold D, uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 Sx).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). fold s. unfold Sx, uE. symmetry. apply u64_of. }
  assert (H12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 N).
  { replace (12%bv : reg) with (xr 12) by (apply bv_eq; reflexivity). rewrite (HR (xr 12)). fold nl. unfold N, uE. symmetry. apply u64_of. }
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small64 by exact Hr64; assumption).
  set (mm := mrestrict H (ms_mem ms)).
  (* [comment removed for export] *)
  assert (Hpts_s : forall i, 0 <= i < rsz E Rs -> rd1 ASEGSN mm (Z_to_bv 64 (AS + i)) <> None).
  { intros i Hi. specialize (Hspts i Hi). unfold rk_rd in Hk1.
    destruct (rg_kind Rs); try discriminate; [exact (proj1 Hspts) | exact (proj1 (proj1 Hspts)) | exact (proj1 (proj1 Hspts)) | exact Hspts]. }
  set (f := fun k : nat => match rd1 ASEGSN mm (Z_to_bv 64 (Sx + Z.of_nat k)) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := List.map f (seq 0 (Z.to_nat N))).
  assert (Hlbs : length bs = Z.to_nat N) by (unfold bs; rewrite length_map, length_seq; reflexivity).
  assert (Hsrc : rdn ASEGSN mm (Z_to_bv 64 Sx) (length bs) = Some bs).
  { rewrite Hlbs. unfold bs. apply rdn_of_rd1; [lia | rewrite Z2Nat.id by lia; unfold two64; lia |].
    intros k Hkk. unfold f. destruct (rd1 ASEGSN mm (Z_to_bv 64 (Sx + Z.of_nat k))) eqn:X; [reflexivity|].
    exfalso. assert (Hkk' : Z.of_nat k < N) by lia.
    apply (Hpts_s (Sx - AS + Z.of_nat k)); [lia|]. replace (AS + (Sx - AS + Z.of_nat k)) with (Sx + Z.of_nat k) by lia. exact X. }
  (* [comment removed for export] *)
  assert (Hpt_d : forall i, 0 <= i < rsz E Rd -> rd1 ASEGSN mm (Z_to_bv 64 (AD + i)) <> None /\ wview ASEGSN mm (Z_to_bv 64 (AD + i)) <> None).
  { intros i Hi. specialize (Hdpts i Hi). unfold rk_wz in Hk0. destruct (rg_kind Rd); try discriminate; [exact Hdpts | exact (proj1 Hdpts)]. }
  assert (Hdst : store_ok ASEGSN mm (Z_to_bv 64 D) (length bs) = true).
  { apply store_ok_from; [lia | rewrite Hlbs, Z2Nat.id by lia; unfold two64; lia|].
    intros i Hi. rewrite Hlbs, Z2Nat.id in Hi by lia. replace (D + i) with (AD + (D - AD + i)) by lia. apply Hpt_d. lia. }
  assert (Hdisj : D + N <= Sx \/ Sx + N <= D).
  { pose proof (rgs_disj_nth E (s_rgs S) j0 j1 Rd Rs HD Hj01 Hj0 Hj1) as X. unfold rg_disj in X. fold (uE E (rg_base Rd)) (uE E (rg_base Rs)) in X.
    fold AD AS in X. lia. }
  assert (HuS : bv_unsigned (Z_to_bv 64 Sx) = Sx) by (apply u_small64; unfold two64 in *; lia).
  assert (HuD : bv_unsigned (Z_to_bv 64 D) = D) by (apply u_small64; unfold two64 in *; lia).
  assert (HOK : mcH mm (Z_to_bv 64 D) (Z_to_bv 64 Sx) N bs).
  { constructor.
    - lia.
    - exact Hlbs.
    - exact Hsrc.
    - exact Hdst.
    - rewrite HuS, HuD. exact Hdisj.
    - rewrite HuS. lia.
    - rewrite HuD. lia. }
  destruct (@ref_memcpy (mkFP (ms_fregs ms) (ms_fcsr ms)) mm (Z_to_bv 64 D) (Z_to_bv 64 Sx) N bs (ms_rom ms) HOK (ms_regs ms) (Z_to_bv 64 r)
              Hret Hra H10 H11 H12) as (regs' & Hms & Hkeep).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (0xd4500 : word) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold CPS_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm. cbn. f_equal. apply bv_eq. reflexivity. }
  set (mem' := wbytes mm (Z_to_bv 64 D) bs).
  try rewrite R1 in Hk. try rewrite Hf0 in Hk. rewrite Hj0 in Hk.
  set (klo := Z.max 0 (fst (irange fs (lsub d (rg_base Rd))))) in *.
  assert (Hklo : klo <= D - AD).
  { unfold win_ok in Hw0. destruct (irange fs (lsub d (rg_base Rd))) as [dlo dhi] eqn:Hdr.
    pose proof (irange_sound E fs (lsub d (rg_base Rd)) HF) as Rdd. rewrite Hdr in Rdd. cbn [fst snd] in Rdd.
    fold (uE E (lsub d (rg_base Rd))) in Rdd.
    destruct (small_diff E d (rg_base Rd) _ _ Rdd) as [[D1 D2]|[D1 D2]]; [|fold D AD in D1; lia].
    fold D AD in D2. unfold klo. try rewrite Hdr. cbn [fst]. lia. }
  apply (den_run_post_win_m ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [] CPS_HAVS j0 Rd klo mem' Hd Hrv Hj0 Hk0).
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - unfold klo. lia.
  - intros w Hw. unfold mem'. apply wbytes_outside; rewrite HuD, Hlbs, Z2Nat.id by lia; [unfold two64 in *; lia|]. fold AD in Hw. lia.
  - intros i Hi. specialize (Hpt_d i Hi). fold AD. destruct Hpt_d as [P1 P2].
    assert (Hor : forall w, mem' w = mm w \/ exists bb, mem' w = Some bb) by (intros w; apply wbytes_or_s).
    split; [exact (mm_or_rd1_s _ _ _ _ (Hor _) P1) | exact (mm_or_wview_s _ _ _ _ (Hor _) P2)].
  - apply Forall_nil.
  - unfold CPS_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->).
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first
      [ (vm_compute in Eh; discriminate Eh)
      | (replace (Z_to_bv 5 0) with (0%bv : reg) by (apply bv_eq; reflexivity); rewrite !getr_zero; reflexivity)
      | (apply Hkeep; cbn [callee_kept]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
  - intros E' ms' model' Ha' Hd' _. exact (Hk E' ms' model' Ha' Hd').
Qed.
End Node.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive wop : Type := OTrack (i : nat) (k0 : positive) (n : nat) | ORecont (i : nat) (k0 : positive) (c : Z).
Definition wop_post (S : sst) (o : wop) : option sst :=
  match o with OTrack i k0 n => rz_trackn_post S i k0 n | ORecont i k0 c => recont_post S i k0 c end.
Fixpoint wops_post (S : sst) (l : list wop) : option sst :=
  match l with [] => Some S | o :: r => match wop_post S o with Some S' => wops_post S' r | None => None end end.
Inductive wnode : Type := WCps | WTrack (i : nat) (k0 : positive) (n : nat) | WRecont (i : nat) (k0 : positive) (c : Z) | WNorm (l : list wop).
Section W.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Definition ppostW (p : wnode) (S : sst) (M : smodel) : option sst :=
  match p with
  | WCps => if cps_chk img S M then Some (cpsw_post S) else None
  | WTrack i k0 n => rz_trackn_post S i k0 n
  | WRecont i k0 c => recont_post S i k0 c
  | WNorm l => wops_post S l
  end.
#[using="Hwx"] Theorem pnodeW_ok : forall p, pnode_ok ASEGSN cfg LIMIT ppostW p.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros p S M S' Hp model0 mem0 E ms model T Hd Hk. destruct p as [|i k0 n|i k0 c|l]; cbn [ppostW] in Hp.
  - destruct (cps_chk img S M) eqn:Hc; [|discriminate]. injection Hp as <-.
    exact (den_cpsw cfg LIMIT model0 mem0 img Hwx S M E ms model T Hc Hd Hk).
  - apply (Hk E ms model); [apply agree_refl|]. exact (den_rz_trackn ASEGSN LIMIT mem0 model0 E S M ms model i k0 n S' Hd Hp).
  - apply (Hk E ms model); [apply agree_refl|]. exact (den_recont ASEGSN LIMIT mem0 model0 E S M ms model i k0 c S' Hd Hp).
  - assert (HW : forall l S0 S1, wops_post S0 l = Some S1 -> DEN ASEGSN LIMIT model0 mem0 E S0 M ms model ->
                   DEN ASEGSN LIMIT model0 mem0 E S1 M ms model /\ s_next S1 = s_next S0).
    { clear. induction l as [|o r IH]; intros S0 S1 H0 Hd0; cbn [wops_post] in H0.
      - injection H0 as <-. split; [exact Hd0 | reflexivity].
      - destruct (wop_post S0 o) as [S2|] eqn:Ho; [|discriminate].
        assert (H2 : DEN ASEGSN LIMIT model0 mem0 E S2 M ms model /\ s_next S2 = s_next S0).
        { destruct o as [i k0 n|i k0 c]; cbn [wop_post] in Ho.
          - split; [exact (den_rz_trackn ASEGSN LIMIT mem0 model0 E S0 M ms model i k0 n S2 Hd0 Ho)|].
            unfold rz_trackn_post in Ho. destruct (nth_error (s_rgs S0) i); [|discriminate]. destruct (rz_trackn_rg _ _ _); [|discriminate]. injection Ho as <-. reflexivity.
          - split; [exact (den_recont ASEGSN LIMIT mem0 model0 E S0 M ms model i k0 c S2 Hd0 Ho)|].
            unfold recont_post in Ho. destruct (nth_error (s_rgs S0) i); [|discriminate]. destruct (recont_rg _ _ _); [|discriminate]. injection Ho as <-. reflexivity. }
        destruct H2 as [Hd2 Hn2]. destruct (IH S2 S1 H0 Hd2) as [Hd1 Hn1]. split; [exact Hd1 | rewrite Hn1; exact Hn2]. }
    destruct (HW l S S' Hp Hd) as [Hd' Hn']. apply (Hk E ms model); [apply agree_refl | exact Hd'].
Qed.
End W.
(* [comment removed for export] *)
