(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChain FxChEnt FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Instance chd_fx : FPState := fx0.

(* [comment removed for export] *)
Definition path_rg (pv : lin) (bs : list Z) : region :=
  RG pv (lconst (Z.of_nat (length bs))) RT (put_bytes TEmpty 0 (List.map BK bs)).
Definition mat_post (S : sst) (pv : lin) (bs : list Z) : sst :=
  SST (s_pc S) (s_regs S) (path_rg pv bs :: s_rgs S) (s_facts S) (s_next S) (s_resv S).
Definition frz_clear (M : smodel) : smodel :=
  SM (sm_maps M) (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) [] (sm_own M).

Lemma u64_small : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64. apply Z.mod_small. exact Hz. Qed.

Section Mat.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_disj_of_pts : forall E (pv : lin) n R, 0 < n -> 0 < rsz E R ->
  (forall w, uE E pv <= w < uE E pv + n -> uE E (rg_base R) + rsz E R <= w \/ w < uE E (rg_base R)) ->
  uE E pv + n <= uE E (rg_base R) \/ uE E (rg_base R) + rsz E R <= uE E pv.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E pv n R Hn HR Hpt.
  destruct (Z_le_gt_dec (uE E pv + n) (uE E (rg_base R))) as [H1|H1]; [left; exact H1|].
  right. destruct (Z_le_gt_dec (uE E (rg_base R) + rsz E R) (uE E pv)) as [H2|H2]; [exact H2|].
  exfalso. set (w := Z.max (uE E pv) (uE E (rg_base R))).
  destruct (Hpt w ltac:(unfold w; lia)) as [H3|H3]; unfold w in H3; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_mat_path : forall E S M ms model (pv : lin) (bs : list Z),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) pv = true -> (1 <= length bs)%nat -> Forall (fun b => 0 <= b < 256) bs ->
  (forall k, (k < length bs)%nat -> exists p, In p (sm_frz M) /\ uE E (fst p) <= uE E pv + Z.of_nat k < uE E (fst p) + uE E (snd p)) ->
  (forall k, (k < length bs)%nat -> mem0 (Z_to_bv 64 (uE E pv + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0))) ->
  DEN segs LIMIT model0 mem0 E (mat_post S pv bs) (frz_clear M) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model pv bs Hd Hwv Hn Hbs Hcov Hm0.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (n := Z.of_nat (length bs)) in *.
  assert (HH : Hof E (frz_clear M) model = Hof E M model) by reflexivity.
  pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
  (* [comment removed for export] *)
  assert (Hpts : forall k, (k < length bs)%nat ->
            alloc_top (m_vmmaps model) <= uE E pv + Z.of_nat k < 0x800000000000 /\ outside E (s_rgs S) (Z_to_bv 64 (uE E pv + Z.of_nat k)) /\
            ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 (uE E pv + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0))).
  { intros k Hk. destruct (Hcov k Hk) as (p & Hp & Hr).
    destruct (Hfrz p Hp _ Hr) as (Htop & Hout & _). split; [exact Htop|]. split; [exact Hout|].
    rewrite (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd (ex_intro _ p (conj Hp Hr))). exact (Hm0 k Hk). }
  assert (Hlo : alloc_top (m_vmmaps model) <= uE E pv /\ uE E pv + n <= 0x800000000000).
  { destruct (Hpts O ltac:(lia)) as (H1 & _). destruct (Hpts (length bs - 1)%nat ltac:(lia)) as (H2 & _).
    unfold n. rewrite Nat2Z.inj_sub in H2 by lia. lia. }
  assert (Hn64 : 0 <= n < two64) by (unfold n, two64 in *; lia).
  assert (Hrsz : forall E', rsz E' (path_rg pv bs) = n) by (intros E'; unfold rsz, path_rg; cbn [rg_size]; rewrite lden_lconst; exact (u64_small n Hn64)).
  (* [comment removed for export] *)
  assert (HRok : forall E', agree (s_next S) E E' -> rg_ok segs E' (ms_mem (restrict (Hof E M model) ms)) (path_rg pv bs)).
  { intros E' Ha. assert (HpvE : lden E' pv = lden E pv) by exact (lden_agree_wf _ E E' pv Hwv Ha).
    unfold rg_ok. rewrite Hrsz. cbn [rg_base rg_kind rg_cont path_rg]. rewrite HpvE. fold (uE E pv).
    split; [lia|]. split; [unfold two64; lia|]. split.
    - intros i Hi. destruct (Hpts (Z.to_nat i) ltac:(unfold n in Hi; lia)) as (_ & _ & Hm). rewrite Z2Nat.id in Hm by lia.
      unfold rd1. rewrite Hm. discriminate.
    - intros p v Hp. rewrite put_bytes_spec in Hp by lia. rewrite tget_empty in Hp.
      destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat (length (List.map BK bs))))%bool eqn:Hc; [|discriminate].
      apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. rewrite length_map in C2.
      rewrite Z.sub_0_r in Hp. rewrite nth_error_map in Hp.
      destruct (nth_error bs (Z.to_nat (Zpos p - 1))) as [b|] eqn:Hb; [|discriminate]. cbn [option_map] in Hp. injection Hp as <-.
      split; [unfold n; lia|].
      destruct (Hpts (Z.to_nat (Zpos p - 1)) ltac:(lia)) as (_ & _ & Hm). rewrite Z2Nat.id in Hm by lia.
      unfold rd1. rewrite Hm. cbn [bden]. rewrite (nth_error_nth _ _ _ Hb). reflexivity. }
  constructor; rewrite ?HH; try assumption.
  - intros E' Ha. cbn [mat_post s_next] in Ha.
    destruct (Hsd E' Ha) as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0, mat_post. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    + constructor; [exact (HRok E' Ha) | exact HG].
    + split; [|exact HD]. apply Forall_forall. intros R HRin. unfold rg_disj.
      unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HRin)) as [Hb1 Hb2].
      assert (HbE : lden E' (rg_base R) = lden E (rg_base R)) by exact (lden_agree_wf _ E E' _ Hb1 Ha).
      assert (HsE : rsz E' R = rsz E R) by (unfold rsz; rewrite (lden_agree_wf _ E E' _ Hb2 Ha); reflexivity).
      rewrite Hrsz. cbn [rg_base path_rg]. rewrite (lden_agree_wf _ E E' pv Hwv Ha), HbE, HsE.
      rewrite Forall_forall in Hrl. destruct (Hrl R HRin) as [Hpos _].
      apply (rg_disj_of_pts E pv n R ltac:(unfold n; lia) Hpos).
      intros w Hw. destruct (Hpts (Z.to_nat (w - uE E pv)) ltac:(unfold n in Hw; lia)) as (_ & Hout & _).
      rewrite Z2Nat.id in Hout by lia. replace (uE E pv + (w - uE E pv)) with w in Hout by lia.
      unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R HRin).
      rewrite u64_small in Hout by (unfold two64; lia). unfold uE. lia.
  - cbn [mat_post s_next]. unfold frz_clear, sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own] in *.
    apply andb_prop in Hwf as [Hwf Hwo]. apply andb_prop in Hwf as [Hwf _]. rewrite Hwf, Hwo. reflexivity.
  - cbn [mat_post s_next s_rgs]. unfold bases_wf in *. cbn [forallb path_rg rg_base rg_size]. rewrite Hwv, lwf_lconst. exact Hbw.
  - intros w Hw Hout. cbn [mat_post s_rgs] in Hout. unfold outside in Hout. apply Forall_inv_tail in Hout. exact (Hzr w Hw Hout).
  - cbn [mat_post s_rgs]. constructor; [|exact Hrl].
    unfold rl_ok. rewrite Hrsz. cbn [rg_base path_rg]. split; [unfold n; lia|]. left. intros w Hw. unfold app_pt.
    split; [right; pose proof (atop_pg_le (m_vmmaps model)); lia|].
    split; [unfold in_shadow, SH_LO, SH_HI; apply andb_false_iff; right; apply Z.ltb_ge; lia | lia].
  - intros p Hp. destruct Hp.
  - apply (own_keep mem0 E E S (mat_post S pv bs) M (frz_clear M) ms ms model model Hwf (agree_refl _ _) eq_refl);
      [| intros w _; reflexivity | intros x Hx; exact Hx | exact Hown].
    intros w Hout. unfold outside in *. cbn [mat_post s_rgs] in Hout. exact (Forall_inv_tail Hout).
Qed.
End Mat.

Section Dir.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
Section Open.
Hypothesis Hfs : sc_fs cfg = true.

#[using="Hfs"] Theorem den_openat_dirref : forall model0 E L M ms model (A B : TSet) (c0 flags : Z) p (fd3 : word),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 56 -> arg L 0 = Some c0 -> fd32 (Z_to_bv 64 c0) = AT_FDCWD32 ->
  arg L 2 = Some flags -> Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) open_ignored_flags = 0 ->
  read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) = CstrOk p ->
  path_eqb p [] = false -> path_has_slash p = false -> path_is_dirref p = true ->
  alloc_fd (m_fds model0) = fd3 -> fd_lookup (m_fds model0) fd3 = None -> (bv_unsigned fd3 < 2 ^ 63) ->
  ranges_avoid (Hof E M model) [(lden E (rget (s_regs L) (rkey a1r)),
                                 cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) path_max)] ->
  (forall e, In e openat_errnos -> forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret e)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') A) ->
  (forall ms' m'', DEN segs LIMIT (with_fds (fd_insert (m_fds model0) fd3 FdDir) model0) mem0 E
                      (ret_post L (lconst (bv_unsigned fd3))) M ms' m'' -> realizes_cfg segs cfg (mkCfg ms' m'') B) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) (t_alt2 A B).
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros model0 E L M ms model A B c0 flags p fd3 Hd H7 H0 Hdfd H2 Hfl Hc Hne Hsl Hdr Hal Hfree Hfd64 Hav HA HB.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17) in *.
  assert (Hx8 : x8 = Z_to_bv 64 56) by exact (a7_const segs E L (restrict H ms) ms 56 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 c0) by exact (gpr_const segs E L (restrict H ms) ms 0 c0 Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (rget (s_regs L) (rkey a1r))) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 2 flags Hsd eq_refl ltac:(lia) H2).
  set (i := sys_input segs ms1 x8) in *.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 c0) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg0).
  assert (A1 : in_arg i 1 = lden E (rget (s_regs L) (rkey a1r))) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg1).
  assert (A2 : in_arg i 2 = Z_to_bv 64 flags) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg2).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  set (pl := lden E (rget (s_regs L) (rkey a1r))) in *.
  set (ci := [(pl, cstr_access_len_aux (in_mem i) pl path_max)]) in *.
  set (ent := FdDir).
  set (f := fd_insert (m_fds model0) fd3 ent).
  assert (Hspo : forall o, syscall_spec i model o <-> record_copyins ci (open_result_spec model (fun fd => with_fds (fd_insert (m_fds model) fd ent))) i model o).
  { intro o. rewrite (syscall_spec_56 i model o Hno). rewrite A0, A1, A2, Hdfd.
    rewrite (openat_rd_reduce AT_FDCWD32 pl (Z_to_bv 64 flags) p i model o eq_refl Hfl Hc Hne Hsl).
    fold ci. destruct o as [eff m' evs|].
    - rewrite !record_copyins_ok_iff. split; intros (eff0 & Ho & ->); exists eff0; split; try reflexivity;
        unfold openat_read_spec in *; rewrite Hdr in *; exact Ho.
    - rewrite !record_copyins_unmodeled_iff. unfold openat_read_spec. rewrite Hdr. reflexivity. }
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  assert (ia : {e : Z | In e openat_errnos}) by (exists ENOMEM; left; reflexivity).
  assert (Hw0 : forall z, lwf (s_next L) (lconst z) = true) by reflexivity.
  assert (HcA : forall e, In e openat_errnos -> forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci (errno_ret e) ci))) m'') A).
  { intros e He m'' Hinv'' Hsb''. apply (HA e He).
    pose proof (den_ret_ci0 segs LIMIT mem0 model0 E L M ms model (lconst (bv_unsigned (errno_ret e))) ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  assert (HcB : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized (with_fds f model) m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci fd3 ci))) m'') B).
  { intros m'' Hinv'' Hsb''. apply HB.
    pose proof (den_ret_ci segs LIMIT mem0 model0 E L M ms model (lconst (bv_unsigned fd3)) f ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 I
             (fun j => match j with inl e => ret_ci (errno_ret (proj1_sig e)) ci | inr _ => ret_ci fd3 ci end)
             (fun j => match j with inl _ => model | inr _ => with_fds f model end)
             (fun _ => [])
             (fun j => match j with inl _ => A | inr _ => B end) (inl ia) (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros [[e He]|[]]; apply Hspo; apply record_copyins_ok_iff; cbn [proj1_sig].
      * exists (mkEffect (errno_ret e) [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. left. exists e. auto.
      * exists (mkEffect fd3 [] []). split.
        2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
            rewrite app_nil_r. reflexivity. }
        apply open_result_ok_iff. right. rewrite Hfm, Hal. split; [exact Hfree|]. unfold f. rewrite <- Hfm. auto.
    + intros eff m' evs Hs. apply Hspo, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
      apply open_result_ok_iff in Hs as [(e & He & -> & -> & ->) | (_ & -> & -> & ->)].
      * exists (inl (exist _ e He)). cbn [proj1_sig]. auto.
      * exists (inr tt). rewrite Hfm, Hal. unfold f. rewrite <- Hfm. auto.
    + intros Hs. apply Hspo, record_copyins_unmodeled_iff in Hs. exact (open_result_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
    + intros [_|_]; [exact Hh | rewrite with_fds_halted; exact Hh].
    + intros [_|_]; [| rewrite with_fds_lazy]; apply lazy_cover_mkH_app; intros x Hx'; exact Hx'.
    + intros [_|_]; [exact Hminv | exact (MInv_with_fds _ f model Hminv)].
    + intros [e|[]]; unfold ret_ci, syscall_effect_accesses; cbn [eff_copyins eff_writes write_accesses]; rewrite app_nil_r; exact Hav.
    + intros [[e He]|[]] m'' Hinv'' Hsb''; cbn [proj1_sig]; [exact (HcA e He m'' Hinv'' Hsb'') | exact (HcB m'' Hinv'' Hsb'')].
  - apply t_alt_sum_nil; [exact ia | |].
    + exact (realizes_cfg_nonempty segs cfg _ _ (HcA ENOMEM ltac:(left; reflexivity) model Hminv (same_but_materialized_refl _))).
    + exact (realizes_cfg_nonempty segs cfg _ _ (HcB (with_fds f model) (MInv_with_fds _ f model Hminv) (same_but_materialized_refl _))).
Qed.
End Open.

(* [comment removed for export] *)
#[using="Type"] Theorem den_read_dir : forall model0 E L M ms model T (fd : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 63 -> arg L 0 = Some fd ->
  fd_lookup (m_fds model0) (fd32 (Z_to_bv 64 fd)) = Some FdDir ->
  access_okb (lden E (argl L 1)) (bv_unsigned (lden E (argl L 2))) = true ->
  (forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret EISDIR)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model T fd Hd H7 H0 Hfd Hok Hk. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  assert (Hx8 : x8 = Z_to_bv 64 63) by exact (a7_const segs E L (restrict H ms) ms 63 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 fd) by exact (gpr_const segs E L (restrict H ms) ms 0 fd Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (argl L 1)) by exact (gpr_lin_k segs E L (restrict H ms) ms 1 Hsd eq_refl ltac:(lia)).
  assert (Hg2 : ms_gpr ms1 2 = lden E (argl L 2)) by exact (gpr_lin_k segs E L (restrict H ms) ms 2 Hsd eq_refl ltac:(lia)).
  set (i := sys_input segs ms1 x8).
  assert (Hno : bv_unsigned (in_sysno i) = 63%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 fd) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg0).
  assert (A1 : in_arg i 1 = lden E (argl L 1)) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg1).
  assert (A2 : in_arg i 2 = lden E (argl L 2)) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg2).
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hspi : forall o, syscall_spec i model o <-> err_ret EISDIR i model o).
  { intro o. rewrite (syscall_spec_63 i model o Hno). rewrite A0, A1, A2. unfold read_spec. rewrite bind_input, bind_get_model.
    rewrite Hfm, Hfd, Hok. reflexivity. }
  assert (Hwv : lwf (s_next L) (lconst (bv_unsigned (errno_ret EISDIR))) = true) by reflexivity.
  assert (Hcont : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (mkEffect (errno_ret EISDIR) [] []))) m'') T).
  { intros m'' Hinv'' Hsb''. apply Hk.
    pose proof (den_ret_ci0 segs LIMIT mem0 model0 E L M ms model (lconst (bv_unsigned (errno_ret EISDIR))) [] m'' Hd Hwv Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 unit (fun _ => mkEffect (errno_ret EISDIR) [] []) (fun _ => model)
             (fun _ => []) (fun _ => T) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspi. apply err_ret_ok_iff. auto.
    + intros eff m' evs Hs. apply Hspi, err_ret_ok_iff in Hs as (-> & -> & ->). exists tt. auto.
    + intros Hs. apply Hspi in Hs. exact (err_ret_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_uninjected. fold i. rewrite Hno. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + intros _. apply ranges_avoid_nil.
    + intros _ m'' Hinv'' Hsb''. exact (Hcont m'' Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    exact (realizes_cfg_nonempty segs cfg _ _ (Hcont model Hminv (same_but_materialized_refl _))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_writev2 : forall model0 E L M ms model (K : TSet) (ch : Z) (b len : lin) (bs : list byte) (n : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 66 -> arg L 0 = Some ch -> arg L 2 = Some 2 -> (ch = 1 \/ ch = 2) ->
  fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch)) ->
  rdn segs (ms_mem ms) (lden E (argl L 1)) 8 = Some (word_to_le_bytes 8 (lden E b)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 8)) 8 = Some (word_to_le_bytes 8 (lden E len)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn segs (ms_mem ms) (lden E b) (length bs) = Some bs ->
  bv_unsigned (lden E len) = Z.of_nat (length bs) -> (1 <= length bs)%nat -> Z.of_nat (length bs) <= n -> n <= 2 ^ 30 ->
  bv_unsigned (lden E (argl L 1)) + 32 <= TASK_SIZE -> bv_unsigned (lden E b) + Z.of_nat (length bs) <= TASK_SIZE ->
  range_avoids (Hof E M model) (lden E (argl L 1)) 32 -> range_avoids (Hof E M model) (lden E b) (length bs) ->
  lwf (s_next L) len = true -> K [] ->
  (forall E' ms' m'', DEN segs LIMIT model0 mem0 E' (wv_post L len n) M ms' m'' -> agree (s_next L) E E' ->
     1 <= bv_unsigned (E' (s_next L)) <= Z.of_nat (length bs) ->
     realizes_cfg segs cfg (mkCfg ms' m'') (t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (bv_unsigned (E' (s_next L)))) bs)) K)) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) (t_emit (map (WriteEv (Z_to_bv 64 ch)) bs) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model K ch b len bs n Hd H7 H0 H2 Hch Hfd0 Hi0 Hi1 Hi2 Hi3 Hbuf Hlen Hnb Hn Hn30 Hiok Hbok Havi Havb Hwl HK0 Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (regs := ms_regs ms).
  set (x8 := ms_reg ms 17).
  set (iov := lden E (argl L 1)) in *.
  pose proof (bv_unsigned_in_range _ iov) as Riov. unfold bv_modulus in Riov. change (2 ^ Z.of_N 64) with two64 in Riov.
  assert (Hx8 : x8 = Z_to_bv 64 66) by exact (a7_const segs E L (restrict H ms) ms 66 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 ch) by exact (gpr_const segs E L (restrict H ms) ms 0 ch Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = iov) by exact (gpr_lin_k segs E L (restrict H ms) ms 1 Hsd eq_refl ltac:(lia)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 2) by exact (gpr_const segs E L (restrict H ms) ms 2 2 Hsd eq_refl ltac:(lia) H2).
  assert (R10 : getr regs 10 = Z_to_bv 64 ch).
  { rewrite <- Hg0. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 0))); [reflexivity|]. exact (getr_gpr ms 0 ltac:(lia)). }
  assert (R11 : getr regs 11 = iov).
  { rewrite <- Hg1. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 1))); [reflexivity|]. exact (getr_gpr ms 1 ltac:(lia)). }
  set (iovs := [(lden E b, lden E len); (Z_to_bv 64 0, Z_to_bv 64 0)]).
  set (bss := [bs; []]).
  assert (R12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs))).
  { cbn [length iovs]. change (Z.of_nat 2) with 2%Z. rewrite <- Hg2. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 2))); [reflexivity|]. exact (getr_gpr ms 2 ltac:(lia)). }
  assert (R17 : getr regs 17 = Z_to_bv 64 66) by exact Hx8.
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hch32 : fd32 (getr regs 10) = Z_to_bv 64 ch) by (rewrite R10; apply fd32_id; rewrite u_small64 by (unfold two64; lia); lia).
  assert (Hfd : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 ch))) by (rewrite Hch32, Hfm; exact Hfd0).
  assert (Hw0 : w_is0 (Z_to_bv 64 ch) = false) by (unfold w_is0, bv_eqb; destruct Hch as [->| ->]; reflexivity).
  assert (Hu16 : bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) = bv_unsigned iov + 16) by (apply u64_small; unfold TASK_SIZE, two64 in *; lia).
  assert (Harr : iov_array segs (ms_mem ms) (getr regs 11) iovs).
  { unfold iovs. cbn [iov_array]. rewrite R11. split; [exact Hi0|]. split; [exact Hi1|]. split; [rewrite Hlen; lia|].
    rewrite Hu16. split; [exact Hi2|]. split; [replace (bv_unsigned iov + 16 + 8) with (bv_unsigned iov + 24) by lia; exact Hi3|].
    split; [rewrite u_small64 by (unfold two64; lia); lia | exact I]. }
  assert (Hbo : iov_bufs_ok iovs).
  { unfold iovs; cbn [iov_bufs_ok]. rewrite Hlen. split; [lia|]. split; [rewrite !u_small64 by (unfold two64; lia); unfold TASK_SIZE; lia | exact I]. }
  assert (Hbb : iov_bufs segs (ms_mem ms) iovs bss).
  { unfold iovs, bss. cbn [iov_bufs]. split; [|split; [|exact I]].
    - unfold word_to_nat. rewrite Hlen, Nat2Z.id. exact Hbuf.
    - unfold word_to_nat. rewrite u_small64 by (unfold two64; lia). reflexivity. }
  assert (Htot : iovs_total iovs = Z.of_nat (length bs)) by (unfold iovs; cbn; rewrite Hlen; rewrite u_small64 by (unfold two64; lia); lia).
  assert (Hcb : concat bss = bs) by (unfold bss; cbn; rewrite !app_nil_r; reflexivity).
  assert (Hiok' : bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE) by (rewrite R11; unfold iovs; cbn [length]; lia).
  pose proof (writev_ch_ok_iff segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss) as Hspec.
  pose proof (writev_ch_no_unmodeled segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss R17 Hfd Hw0 R12
                ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)) as Hnu.
  rewrite <- (sys_input_pend segs ms (getr regs 17) Hrom) in Hnu.
  assert (Hx8' : getr regs 17 = x8) by reflexivity. rewrite Hx8' in Hnu.
  set (CA := import_iovecs_accesses (mrb segs (ms_mem ms)) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  set (EF := fun j : wr_index bs => ret_ci (Z_to_bv 64 (Z.of_nat (proj1_sig j))) (CA ++ (iov_prefix_accesses iovs (proj1_sig j) ++ []))).
  assert (Hspr : forall eff m' evs, syscall_spec (sys_input segs ms1 x8) model (Ok eff m' evs) <->
            exists j : wr_index bs, eff = EF j /\ m' = model /\ evs = map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs)).
  { intros eff m' evs. unfold ms1. rewrite (sys_input_pend segs ms x8 Hrom). fold regs. rewrite <- Hx8'.
    rewrite (Hspec eff m' evs R17 Hfd Hw0 R12 ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)).
    rewrite Hcb. split.
    - intros (k & Hk' & -> & -> & ->). exists (exist _ k Hk'). unfold EF. cbn [proj1_sig]. auto.
    - intros ([k Hk'] & -> & -> & ->). exists k. unfold EF. cbn [proj1_sig]. auto. }
  (* [comment removed for export] *)
  assert (HCA : ranges_avoid H CA).
  { unfold CA, import_iovecs_accesses. unfold iovs. cbn [length]. change (Z.of_nat 2) with 2%Z.
    replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 1)) with false by reflexivity.
    replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 0)) with false by reflexivity.
    rewrite u_small64 by (unfold two64; lia). replace (IOV_MAX <? 2)%Z with false by reflexivity.
    destruct (negb (access_okb (getr regs 11) (16 * 2))); [apply ranges_avoid_nil|].
    change (word_to_nat (Z_to_bv 64 2)) with 2%nat. cbn [copy_iovecs_accesses].
    apply ranges_avoid_cons; [rewrite R11; exact (ra_le H iov 32 16 ltac:(lia) Havi)|].
    destruct (read_iovec_entry (mrb segs (ms_mem ms)) (getr regs 11)); try apply ranges_avoid_nil.
    apply ranges_avoid_cons; [|destruct (read_iovec_entry (mrb segs (ms_mem ms)) (getr regs 11 + 16)%bv); apply ranges_avoid_nil].
    rewrite R11. intros kk Hkk. replace (woff (iov + 16)%bv kk) with (woff iov (16 + kk)); [apply Havi; lia|].
    unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_add_unsigned. unfold bv_wrap.
    change (bv_unsigned (16 : word)) with 16. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  assert (Hacc : forall j : wr_index bs, ranges_avoid H (syscall_effect_accesses (EF j))).
  { intros [k Hk']. unfold EF, ret_ci, syscall_effect_accesses. cbn [eff_copyins eff_writes proj1_sig]. rewrite !app_nil_r.
    apply ranges_avoid_app; [exact HCA|].
    unfold iovs. cbn [iov_prefix_accesses].
    destruct k as [|k]; [lia|].
    destruct (Nat.eqb (word_to_nat_bounded (lden E len) (Datatypes.S k)) 0) eqn:Ez.
    - cbn [iov_prefix_accesses]. destruct (word_to_nat_bounded (Z_to_bv 64 0) (Datatypes.S k)) eqn:Ez2; cbn [Nat.eqb].
      + apply ranges_avoid_nil.
      + exfalso. pose proof (word_to_nat_bounded_eq_min (Z_to_bv 64 0) (Datatypes.S k)) as X. rewrite Ez2 in X.
        unfold word_to_nat in X. rewrite u_small64 in X by (unfold two64; lia). lia.
    - apply ranges_avoid_cons.
      + apply (ra_le H (lden E b) (length bs)); [|exact Havb].
        pose proof (word_to_nat_bounded_eq_min (lden E len) (Datatypes.S k)) as X.
        rewrite X. unfold word_to_nat. rewrite Hlen, Nat2Z.id. lia.
      + destruct (Datatypes.S k - word_to_nat_bounded (lden E len) (Datatypes.S k))%nat as [|kk]; [apply ranges_avoid_nil|].
        cbn [iov_prefix_accesses]. destruct (word_to_nat_bounded (Z_to_bv 64 0) (Datatypes.S kk)) eqn:Ez2; cbn [Nat.eqb].
        * apply ranges_avoid_nil.
        * exfalso. pose proof (word_to_nat_bounded_eq_min (Z_to_bv 64 0) (Datatypes.S kk)) as X. rewrite Ez2 in X.
          unfold word_to_nat in X. rewrite u_small64 in X by (unfold two64; lia). lia. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 (wr_index bs) EF (fun _ => model)
             (fun j => map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs))
             (fun j => t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (proj1_sig j) bs)) K) (wr_full bs Hnb) (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros j. apply Hspr. exists j. auto.
    + intros eff m' evs Hs. apply Hspr in Hs as (j & -> & -> & ->). exists j. auto.
    + exact Hnu.
    + intros eff. apply not_spurious_uninjected. cbn [in_sysno sys_input]. rewrite Hx8. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + exact Hacc.
    + intros [k Hk'] m'' Hinv'' Hsb''. cbn [proj1_sig].
      set (w := Z_to_bv 64 (Z.of_nat k)).
      assert (Hwu : bv_unsigned w = Z.of_nat k) by (unfold w; apply u_small64; unfold two64; lia).
      pose proof (den_ret_fresh segs LIMIT mem0 model0 E L M ms model w (fun x => [FRange x 1 n; FRange (lsub len x) 0 n])
                    (CA ++ (iov_prefix_accesses iovs k ++ [])) m'' Hd) as HD'.
      assert (HD2 : DEN segs LIMIT model0 mem0 (upd E (s_next L) w) (wv_post L len n) M
                  (advance_past_svc (apply_effect ms1 (EF (exist _ k Hk')))) m'').
      { apply HD'; [|exact Hinv'' | exact Hsb''].
        intros E' Ha'. assert (He : E' (s_next L) = w) by (rewrite <- (Ha' (s_next L) ltac:(lia)); unfold upd; rewrite Pos.eqb_refl; reflexivity).
        assert (Hle : lden E' len = lden E len).
        { rewrite (lden_agree_wf (s_next L) E E' len Hwl); [reflexivity|].
          intros x Hx. rewrite <- (Ha' x ltac:(lia)). unfold upd. destruct (Pos.eqb x (s_next L)) eqn:Ex; [apply Pos.eqb_eq in Ex; lia | reflexivity]. }
        constructor; [|constructor; [|constructor]].
        - cbn [fact_ok]. rewrite lden_lvar, He, Hwu. lia.
        - cbn [fact_ok]. rewrite lden_lsub, lden_lvar, He, Hle. rewrite bv_sub_unsigned, Hwu, Hlen. unfold bv_wrap.
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
      eapply rzc_conseq; [apply (Hk (upd E (s_next L) w) _ m'' HD2 (agree_upd _ E w))|].
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu. lia.
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu, Nat2Z.id. apply t_eq_refl.
  - apply (t_alt_wall (Z_to_bv 64 ch) bs K HK0 Hnb).
Qed.
End Dir.

(* [comment removed for export] *)
Definition path_rg2 (pv sz : lin) (bs : list Z) : region := RG pv sz RT (put_bytes TEmpty 0 (List.map BK bs)).
Definition mat_post2 (S : sst) (pv sz : lin) (bs : list Z) : sst :=
  SST (s_pc S) (s_regs S) (path_rg2 pv sz bs :: s_rgs S) (s_facts S) (s_next S) (s_resv S).

Section Mat2.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_mat_rt : forall E S M ms model (pv sz : lin) (bs : list Z),
  DEN segs LIMIT model0 mem0 E S M ms model ->
  lwf (s_next S) pv = true -> lwf (s_next S) sz = true -> 0 < uE E sz -> Z.of_nat (length bs) <= uE E sz ->
  Forall (fun b => 0 <= b < 256) bs ->
  (forall w, uE E pv <= w < uE E pv + uE E sz ->
     alloc_top (m_vmmaps model) <= w < 0x800000000000 /\ outside E (s_rgs S) (Z_to_bv 64 w) /\
     rd1 segs (ms_mem (restrict (Hof E M model) ms)) (Z_to_bv 64 w) <> None) ->
  (forall k, (k < length bs)%nat -> rd1 segs (ms_mem (restrict (Hof E M model) ms)) (Z_to_bv 64 (uE E pv + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0))) ->
  DEN segs LIMIT model0 mem0 E (mat_post2 S pv sz bs) (frz_clear M) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model pv sz bs Hd Hwv Hws Hsz0 Hlen Hbs Hpts Hm0.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HH : Hof E (frz_clear M) model = Hof E M model) by reflexivity.
  pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
  assert (Hlo : alloc_top (m_vmmaps model) <= uE E pv /\ uE E pv + uE E sz <= 0x800000000000).
  { destruct (Hpts (uE E pv) ltac:(lia)) as (H1 & _). destruct (Hpts (uE E pv + uE E sz - 1) ltac:(lia)) as (H2 & _). lia. }
  assert (HRok : forall E', agree (s_next S) E E' -> rg_ok segs E' (ms_mem (restrict (Hof E M model) ms)) (path_rg2 pv sz bs)).
  { intros E' Ha. assert (HpvE : lden E' pv = lden E pv) by exact (lden_agree_wf _ E E' pv Hwv Ha).
    assert (HszE : rsz E' (path_rg2 pv sz bs) = uE E sz) by (unfold rsz, path_rg2; cbn [rg_size]; unfold uE; rewrite (lden_agree_wf _ E E' sz Hws Ha); reflexivity).
    unfold rg_ok. rewrite HszE. cbn [rg_base rg_kind rg_cont path_rg2]. rewrite HpvE. fold (uE E pv).
    split; [lia|]. split; [unfold two64; lia|]. split.
    - intros i Hi. destruct (Hpts (uE E pv + i) ltac:(lia)) as (_ & _ & Hm). exact Hm.
    - intros p v Hp. rewrite put_bytes_spec in Hp by lia. rewrite tget_empty in Hp.
      destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat (length (List.map BK bs))))%bool eqn:Hc; [|discriminate].
      apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. rewrite length_map in C2.
      rewrite Z.sub_0_r in Hp. rewrite nth_error_map in Hp.
      destruct (nth_error bs (Z.to_nat (Zpos p - 1))) as [b|] eqn:Hb; [|discriminate]. cbn [option_map] in Hp. injection Hp as <-.
      split; [lia|].
      pose proof (Hm0 (Z.to_nat (Zpos p - 1)) ltac:(lia)) as Hm. rewrite Z2Nat.id in Hm by lia.
      rewrite Hm. cbn [bden]. rewrite (nth_error_nth _ _ _ Hb). reflexivity. }
  constructor; rewrite ?HH; try assumption.
  - intros E' Ha. cbn [mat_post2 s_next] in Ha.
    destruct (Hsd E' Ha) as (Hpc1 & Hsv1 & Hrv & HR & HG & HD & HF & Hfrm).
    unfold sden0, mat_post2. cbn [s_pc s_regs s_rgs s_facts s_resv].
    split; [exact Hpc1|]. split; [exact Hsv1|]. split; [exact Hrv|]. split; [exact HR|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    + constructor; [exact (HRok E' Ha) | exact HG].
    + split; [|exact HD]. apply Forall_forall. intros R HRin. unfold rg_disj.
      unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HRin)) as [Hb1 Hb2].
      assert (HbE : lden E' (rg_base R) = lden E (rg_base R)) by exact (lden_agree_wf _ E E' _ Hb1 Ha).
      assert (HsE : rsz E' R = rsz E R) by (unfold rsz; rewrite (lden_agree_wf _ E E' _ Hb2 Ha); reflexivity).
      assert (HszE : rsz E' (path_rg2 pv sz bs) = uE E sz) by (unfold rsz, path_rg2; cbn [rg_size]; unfold uE; rewrite (lden_agree_wf _ E E' sz Hws Ha); reflexivity).
      rewrite HszE. cbn [rg_base path_rg2]. rewrite (lden_agree_wf _ E E' pv Hwv Ha), HbE, HsE.
      rewrite Forall_forall in Hrl. destruct (Hrl R HRin) as [Hpos _].
      apply (rg_disj_of_pts E pv (uE E sz) R Hsz0 Hpos).
      intros w Hw. destruct (Hpts w Hw) as (_ & Hout & _).
      unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R HRin).
      rewrite u64_small in Hout by (unfold two64; lia). unfold uE. lia.
  - cbn [mat_post2 s_next]. unfold frz_clear, sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own] in *.
    apply andb_prop in Hwf as [Hwf Hwo]. apply andb_prop in Hwf as [Hwf _]. rewrite Hwf, Hwo. reflexivity.
  - cbn [mat_post2 s_next s_rgs]. unfold bases_wf in *. cbn [forallb path_rg2 rg_base rg_size]. rewrite Hwv, Hws. exact Hbw.
  - intros w Hw Hout. cbn [mat_post2 s_rgs] in Hout. unfold outside in Hout. apply Forall_inv_tail in Hout. exact (Hzr w Hw Hout).
  - cbn [mat_post2 s_rgs]. constructor; [|exact Hrl].
    unfold rl_ok. assert (HszE : rsz E (path_rg2 pv sz bs) = uE E sz) by reflexivity. rewrite HszE. cbn [rg_base path_rg2].
    split; [lia|]. left. intros w Hw. unfold app_pt.
    destruct (Hpts w Hw) as (Hw1 & _ & _).
    split; [right; pose proof (atop_pg_le (m_vmmaps model)); lia|].
    split; [unfold in_shadow, SH_LO, SH_HI; apply andb_false_iff; right; apply Z.ltb_ge; lia | lia].
  - intros p Hp. destruct Hp.
  - apply (own_keep mem0 E E S (mat_post2 S pv sz bs) M (frz_clear M) ms ms model model Hwf (agree_refl _ _) eq_refl);
      [| intros w _; reflexivity | intros x Hx; exact Hx | exact Hown].
    intros w Hout. unfold outside in *. cbn [mat_post2 s_rgs] in Hout. exact (Forall_inv_tail Hout).
Qed.
End Mat2.
