(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothInit BsImages BsPlanImages BsHSTab BsStartupHSF BsStartupCerts BsMainVM BsMainState BsMainFacts BsMainLazyChk BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsMainSyms BerfLia.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export BsMainLazyChk.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition SHOFF : Z := 0x7fff8000.

Definition SW (a n : Z) : Z * Z := (SHOFF + a / 8, (a + n) / 8 - a / 8).

Definition VISZ0 (sp0z brk0z : Z) (X : pm_syms) : list (Z * Z) :=
  [(ps_b23 X, 4096); (ps_b22 X, 0x800000); (ps_b21 X, 0x100000); (ps_b20 X, 4096);
   (if ps_granted X then (brk0z, 8192) else (ps_b19r X + 4096, 4096)); (ps_b16 X, 0xb09000); (ps_b12 X, 4096); (ps_b11 X, 4096);
   (ps_b10 X, 0x10000); (ps_b09 X, 4096); (pm_region_info X, 4096); (ps_b05 X, 0x38e000); (ps_b04 X, 0x10000);
   (0x10000, 0x6d8000); (page_down sp0z - 0x800000, 0x800000800000 - page_down sp0z)].
Definition VISZ (sp0z brk0z : Z) (X : pm_syms) : list (Z * Z) := VISZ0 sp0z brk0z X ++ [(ps_b13 X, 4096)].

Definition PM_S (sp0z brk0z : Z) (X : pm_syms) : list (Z * Z) :=
  (ps_b22 X, 0x800000) :: map (fun p => SW (fst p) (snd p)) (VISZ sp0z brk0z X).

Definition PM_ZR (sp0z : Z) (X : pm_syms) : list (Z * Z) :=
  [(ps_b22 X, 0x800000); (0x2008fff7000, 0xdfff0001000); (0x7fff7000, 0x10000000)].

Definition PM_S_PAGES : Z := 68900.

Definition DG_visg (g : bool) : list (lin * lin) := DG_vis g ++ [(pg K_B13, (4096, []))].

Section LZ.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H BothInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  Let X := Xof g E.
  Let brk0z := bv_unsigned brk0.
  Let sp0z := bv_unsigned sp0.
  Let KN := kn_arith_ok _ _ _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
  Let D : hs_digest ch = DGX g cls := proj1 (open_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Let LZC : lz_check g cls ch = true := HS_lz_check h ch Hh.

  Lemma lzc_parts :
    all_pairs_disjB (mkbc (kn_arith (kn ch))) (KPSX g) = true
    /\ cross_disjB (mkbc (kn_arith (kn ch))) (APPS g) (LZS g cls) = true
    /\ placedB (mkbc (kn_arith (kn ch))) (KPS g ++ [(pg K_B13, pgo 4096 K_B13)]) = true
    /\ (g = true -> has_fact (kn ch) (KRange (EVar 5) 1768 524276) = true)
    /\ vis_nwB (mkbc (kn_arith (kn ch))) (a_vis ch ++ a_ghost ch) = true
    /\ a_ghost ch = [(EMd Instr.M_MUL (ELit 4096) (EVar K_B13), ELit 4096)].
  Proof.
    pose proof LZC as H. unfold lz_check in H. cbv zeta in H.
    apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    repeat split; try assumption.
    - intros Hg. rewrite Hg in H4. exact H4.
    - apply (list_eqb_eq pair_eqb) in H6; [exact H6|]. intros x y Hxy. unfold pair_eqb in Hxy. apply andb_prop in Hxy as [Ha Hb].
      apply expr_eqb_eq in Ha. apply expr_eqb_eq in Hb. destruct x as [x1 x2], y as [y1 y2]. cbn [fst snd] in Ha, Hb. subst. reflexivity.
  Qed.

  Lemma facts : (cls <= 1)%nat
    /\ 0 <= vE E K_R06 <= 15 /\ (4096 * vE E K_B06) mod 65536 = 4096 * vE E K_R06 /\ 4295491576 <= vE E K_B06 <= 34326181871
    /\ 4294901760 <= vE E 0 <= 4294967295 /\ 1 <= vE E K_TID <= 4194303
    /\ qlo cls <= vE E 6 <= qhi cls /\ wlo cls <= vE E 10 <= whi cls
    /\ 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 = sp0z /\ 16 * vE E 10 = sp0z mod 4096
    /\ 4096 * vE E 5 = brk0z /\ vE E 1 = Z.of_nat (length (in_argv inp)) /\ vE E 2 = Z.of_nat (length (in_envp inp))
    /\ pm_stack_top sp0z = 32768 * vE E 0 + 4096 * vE E 6 + (if Z.leb 11 (vE E 10) then 4096 else 0)
    /\ TOP model = sp0z - 8388608
    /\ 32768 * vE E 0 + 4096 * vE E 6 = page_down sp0z /\ 0 <= vE E 6 <= 7 /\ 0 <= vE E 10 <= 255
    /\ 0x7fff80000000 <= sp0z <= 0x800000000000.
  Proof.
    pose proof (proj2 (open_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)) as F. cbv zeta in F.
    destruct F as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm).
    assert (V610 : 0 <= vE E 6 <= 7 /\ 0 <= vE E 10 <= 255).
    { clearbody D LZC. clear -V6 V10 Hcls. destruct (hole_class h) as [|[|]]; cbn [qlo qhi wlo whi] in V6, V10; lia. }
    assert (PGD : 32768 * vE E 0 + 4096 * vE E 6 = page_down sp0z).
    { unfold page_down. pose proof (Z.div_mod (bv_unsigned sp0) 4096 ltac:(lia)). unfold sp0z in *. lia. }
    assert (VSP : 0x7fff80000000 <= sp0z <= 0x800000000000).
    { pose proof Vsp as (Hlo & Hhi & _). change sp_window_lo with 0x7fff80000000 in Hlo. change sp_window_hi with 0x800000000000 in Hhi. unfold sp0z. lia. }
    repeat split; assumption || lia.
  Qed.

  Lemma VISZ0_eq :
    map (fun p => (uE E (fst p), uE E (snd p))) (a_vis ch) = VISZ0 sp0z brk0z X
    /\ map (fun p => (uE E (fst p), uE E (snd p))) (a_ghost ch) = [(ps_b13 X, 4096)].
  Proof.
    pose proof facts as (_ & _ & REL & _ & _ & _ & _ & _ & _ & _ & BRK' & _ & _ & _ & _ & PGD & _).
    assert (BRK : g = true -> 4096 * vE E 5 = brk0z) by (intros; exact BRK').
    destruct lzc_parts as (_ & _ & _ & _ & NW & GH).
    pose proof (vis_nwB_sound _ _ _ _ _ KN NW) as V. rewrite !map_app in V. rewrite GH in V |- *.
    cbn [map app fst snd] in V. apply app_inj_tail in V as [V1 V2]. split.
    2: { cbn [map fst snd]. rewrite V2. unfold X, Xof. cbn [ps_b13 lin_of].
         change (lscale 4096 (0, [(1, EVar K_B13)])) with (pg K_B13). change (snorm 4096, []) with (lconst 4096). zzcrush. }
    rewrite V1.
    transitivity (map (fun q : lin * lin => (lden E (fst q), lden E (snd q))) (map (fun p => (lin_of (fst p), lin_of (snd p))) (a_vis ch))).
    { rewrite map_map. reflexivity. }
    rewrite (f_equal dg_vis D : map _ (a_vis ch) = DG_vis g).
    unfold VISZ0, X. rewrite (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL). rewrite <- PGD. unfold Xof.
    cbn [ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted Xof].
    clearbody D LZC. destruct g; [specialize (BRK eq_refl)|]; cbn [DG_vis map fst snd app]; zzcrush.
  Qed.

  Lemma BRKg : g = true -> 4096 * vE E 5 = brk0z.
  Proof. intros _. pose proof facts as F. unfold brk0z. lia. Qed.

  Lemma KPS_eq : map (sivZ E) (KPS g) = pm_kernel_placed X.
  Proof.
    unfold KPS, KPSk, pm_kernel_placed, X, Xof.
    cbn [ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted].
    clear. destruct g; cbn [map app]; unfold sivZ, ksiv; cbn [fst snd]; zzcrush.
  Qed.

  Lemma KPS_placed : Forall (pm_placed sp0z) (pm_kernel_placed X) /\ pm_placed sp0z (ps_b13 X, 4096).
  Proof.
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP).
    destruct lzc_parts as (_ & _ & B & _). apply (placedB_sound _ _ _ _ KN) in B.
    rewrite Forall_app in B. destruct B as [B1 B2].
    assert (STK1 : lden E (fst STKS) = page_down sp0z - 8388608) by (unfold STKS, lden; cbn [fst snd tden]; rewrite ?uE_var; lia).
    assert (STK2 : lden E (snd STKS) = page_down sp0z + 281474968322048) by (unfold STKS, lden; cbn [fst snd tden]; rewrite ?uE_var; lia).
    assert (PD : page_down sp0z <= sp0z) by (unfold page_down; lia).
    assert (ONE : forall s, 4096 <= lden E (fst s) /\ lden E (snd s) <= 2 ^ 47
                 /\ (lden E (snd s) <= lden E (fst STKS) \/ lden E (snd STKS) <= lden E (fst s))
                 /\ (lden E (snd s) <= 65536 \/ 7241728 <= lden E (fst s))
                 /\ (lden E (snd s) <= 2147446784 \/ 17594333495296 <= lden E (fst s)) ->
                 lden E (fst s) mod 4096 = 0 -> lden E (fst s) <= lden E (snd s) -> pm_placed sp0z (sivZ E s)).
    { intros s (H1 & H5 & H2 & H3 & H4) Hal Hsz. unfold pm_placed, sivZ, pm_top, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO. cbn [fst snd].
      rewrite STK1, STK2 in H2. repeat split; lia. }
    split.
    - rewrite <- KPS_eq. apply Forall_map. unfold KPS. apply Forall_map. apply Forall_forall. intros kc Hkc.
      pose proof (proj1 (Forall_forall _ _) (KPSk_pos g) kc Hkc) as Hpos. cbv beta in Hpos. destruct (ksiv_den E kc) as [D1 D2].
      apply ONE.
      + apply (proj1 (Forall_forall _ _) B1). unfold KPS. apply in_map. exact Hkc.
      + rewrite D1. rewrite Z.mul_comm. apply Z_mod_mult.
      + rewrite D1, D2. lia.
    - apply Forall_inv in B2. replace (ps_b13 X, 4096) with (sivZ E (pg K_B13, pgo 4096 K_B13)).
      + apply ONE; [exact B2| |]; unfold pg, pgo, lden; cbn [fst snd tden]; rewrite ?Z.add_0_r, ?Z.add_0_l; [rewrite Z.mul_comm; apply Z_mod_mult | lia].
      + unfold sivZ, X, Xof, pg, pgo, lden. cbn [fst snd tden ps_b13]. rewrite ?uE_var. f_equal; lia.
  Qed.

  Lemma pm_syms_ok_open : pm_syms_ok sp0z brk0z 0 X.
  Proof.
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & _).
    destruct KPS_placed as (B & _). destruct lzc_parts as (AP & _ & _ & G5 & _).
    apply (all_pairs_disjB_sound _ _ _ _ KN) in AP. unfold KPSX in AP. rewrite map_app, KPS_eq in AP.
    split.
    - unfold X, Xof. cbn [ps_tid]. lia.
    - exact B.
    - clearbody D LZC. clear -AP. revert AP. generalize (pm_kernel_placed X) as l. intros l AP.
      induction l as [|[a n] l IH]; [exact I|]. cbn [app pairwise_apart] in AP. destruct AP as [A1 A2].
      split; [|exact (IH A2)]. rewrite Forall_app in A1. exact (proj1 A1).
    - unfold pm_space_beg, X, Xof. cbn [ps_b06]. pose proof (Z.div_mod (4096 * vE E K_B06) 65536 ltac:(lia)) as H. rewrite REL in H.
      split; [lia|]. replace (4096 * vE E K_B06 / 65536 * 65536 + 65536) with ((4096 * vE E K_B06 / 65536 + 1) * 65536) by lia. apply Z_mod_mult.
    - intros Hg. unfold X, Xof in Hg. cbn [ps_granted] in Hg. specialize (G5 Hg).
      pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ G5) as R5. rewrite uE_var in R5. rewrite <- (BRKg Hg). unfold ALOWSH_LO. split; [lia|].
      rewrite Hg in AP. cbn [map app] in AP. unfold sivZ in AP. cbn [fst snd] in AP.
      replace (lden E (pg 5)) with (4096 * vE E 5) in AP by (unfold pg, lden; cbn [fst snd tden]; rewrite ?uE_var; lia).
      replace (lden E (pgo 8192 5)) with (8192 + 4096 * vE E 5) in AP by (unfold pgo, lden; cbn [fst snd tden]; rewrite ?uE_var; lia).
      clearbody D LZC. clear -AP. revert AP. generalize (pm_kernel_placed X) as l. intros l AP.
      induction l as [|[a n] l IH]; [constructor|]. cbn [app pairwise_apart] in AP. destruct AP as [A1 A2].
      rewrite Forall_app in A1. destruct A1 as [_ A1]. apply Forall_inv in A1. cbn [fst snd] in A1.
      constructor; [cbn [fst snd]; lia | exact (IH A2)].
  Qed.

  Definition zz_ok (l : list (Z * Z)) : Prop := Forall (fun p => 0 <= fst p < 2 ^ 64 /\ 0 <= snd p < 2 ^ 64) l.
  Definition zin (z : Z) (l : list (Z * Z)) : bool := existsb (fun p => (fst p <=? z) && (z <? fst p + snd p)) l.
  Definition zpin (z : Z) (l : list (Z * Z)) : bool := existsb (fun p => (fst p <=? z) && (z + 4096 <=? fst p + snd p)) l.

  Lemma in_rangesb_zz : forall l x, zz_ok l -> in_rangesb x (zz2ww l) = zin (bv_unsigned x) l.
  Proof.
    induction l as [|[a n] l IH]; intros x Hok; [reflexivity|]. apply Forall_cons_iff in Hok as [[H1 H2] Hok]. cbn [fst snd] in *.
    unfold zz2ww. cbn [map]. rewrite in_rangesb_cons. unfold zin. cbn [existsb fst snd]. fold (zz2ww l). fold (zin (bv_unsigned x) l).
    rewrite (IH x Hok). unfold zin_rangeb. cbn [fst snd]. rewrite !u_of_Z by lia. reflexivity.
  Qed.
  Lemma in_ivs_zz : forall l z, zz_ok l -> in_ivs z (zz2ww l) = zin z l.
  Proof.
    induction l as [|[a n] l IH]; intros z Hok; [reflexivity|]. apply Forall_cons_iff in Hok as [[H1 H2] Hok]. cbn [fst snd] in *.
    unfold zz2ww, in_ivs, zin. cbn [map existsb fst snd]. fold (zz2ww l). rewrite !u_of_Z by lia. f_equal. exact (IH z Hok).
  Qed.
  Lemma page_in_ranges_zz : forall l p, zz_ok l -> page_in_ranges p (zz2ww l) = zpin (bv_unsigned p) l.
  Proof.
    induction l as [|[a n] l IH]; intros p Hok; [reflexivity|]. apply Forall_cons_iff in Hok as [[H1 H2] Hok]. cbn [fst snd] in *.
    unfold zz2ww, page_in_ranges, zpin. cbn [map existsb fst snd]. fold (zz2ww l). rewrite !u_of_Z by lia. unfold page_size. f_equal. exact (IH p Hok).
  Qed.
  Lemma zin_spec : forall z l, zin z l = true <-> exists p, In p l /\ fst p <= z < fst p + snd p.
  Proof.
    intros z l. unfold zin. rewrite existsb_exists. split; intros [p [A B]]; exists p; split; auto.
    - apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
    - apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma KPS_len : Forall (fun p => snd p mod 4096 = 0 /\ 0 < snd p) (pm_kernel_placed X).
  Proof. unfold pm_kernel_placed. destruct (ps_granted X); cbn [app]; repeat constructor. Qed.

  Lemma KB : let K := pm_kernel_placed X in
    Forall (fun p => 4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608) K
    /\ (4096 <= ps_b13 X /\ ps_b13 X + 4096 <= page_down sp0z - 8388608).
  Proof.
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP).
    destruct KPS_placed as [B1 B2].
    assert (PG : forall a n, a mod 4096 = 0 -> n mod 4096 = 0 -> a + n <= pm_top sp0z -> a + n <= page_down sp0z - 8388608).
    { intros a n Ha Hn Hle. unfold pm_top in Hle. clearbody D LZC. clear -Ha Hn Hle PGD SP V10'. lia. }
    cbv zeta. split.
    - apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) B1 p Hp) as (H1 & H2 & H3 & H4 & H5).
      pose proof (proj1 (Forall_forall _ _) KPS_len p Hp) as [Hn _].
      split; [exact H2 | exact (PG _ _ H1 Hn H3)].
    - destruct B2 as (H1 & H2 & H3 & H4 & H5). cbn [fst snd] in H1, H2, H3.
      split; [exact H2 | exact (PG _ 4096 H1 eq_refl H3)].
  Qed.
  Lemma KBAND_in : forall p, In p (pm_kernel_placed X) \/ p = (ps_b13 X, 4096) ->
    (fst p + snd p <= 65536 \/ 7241728 <= fst p) /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p).
  Proof.
    intros p Hp. destruct KPS_placed as [B1 B2].
    assert (HP : pm_placed sp0z p) by (destruct Hp as [Hp| ->]; [exact (proj1 (Forall_forall _ _) B1 p Hp) | exact B2]).
    destruct HP as (_ & _ & _ & H4 & H5). unfold AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in H4, H5. exact (conj H4 H5).
  Qed.

  Ltac prep :=
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP);
    let B := fresh "B" in let Bg := fresh "Bg" in let B13 := fresh "B13" in
    pose proof KB as B; cbv zeta in B; destruct B as [B B13];
    unfold pm_kernel_placed in B; rewrite Forall_app in B; destruct B as [B Bg];
    unfold X, Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]); cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0.
  Ltac zlists :=
    unfold PM_LAZY, PM_S, PM_ZR, PM_NOACC, PM_MAPS, PM_REM, VISZ, VISZ0, SW, pm_meta_map;
    rewrite ?(RI_lin X (4096 * vE E K_B06) (vE E K_R06) eq_refl) by assumption;
    unfold X, Xof; cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted map app fst snd].

  Ltac solve_forall := repeat (first [apply Forall_nil | apply Forall_cons | (rewrite Forall_app; split)
                                     | match goal with |- Forall _ ((if ?c then _ else _) ++ _) => destruct c | |- Forall _ (if ?c then _ else _) => destruct c end]).

  Lemma zz_ok_lazy : zz_ok (PM_LAZY sp0z X).
  Proof. prep. zlists. clearbody D LZC. unfold zz_ok. solve_forall; cbn [fst snd]; lia. Qed.

  Lemma page_allowedb_flat_map : forall {T} (f : T -> list (Z * Z)) l p,
    page_allowedb (flat_map f l) p = true -> exists q, In q l /\ page_allowedb (f q) p = true.
  Proof.
    intros T f l p H. unfold page_allowedb in H. apply existsb_exists in H as [iv [Hin Hiv]].
    apply in_flat_map in Hin as [q [Hq Hiv']]. exists q. split; [exact Hq|]. unfold page_allowedb. apply existsb_exists. exists iv. auto.
  Qed.
  Lemma page_allowedb_In : forall A p, page_allowedb A p = true -> exists iv, In iv A /\ fst iv <= bv_unsigned p /\ bv_unsigned p + 4096 <= snd iv.
  Proof.
    intros A p H. unfold page_allowedb in H. apply existsb_exists in H as [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists iv. unfold page_size in H2. auto.
  Qed.
  Lemma page_in_sivs : forall L p, Forall (siv_wf E) L -> page_in_ranges p (sivs_den E L) = true ->
    exists s, In s L /\ lden E (fst s) <= bv_unsigned p /\ bv_unsigned p + 4096 <= lden E (snd s).
  Proof.
    induction L as [|s L IH]; intros p WF H; [cbn in H; discriminate|]. apply Forall_cons_iff in WF as [[W1 [W2 W3]] WF].
    cbn [sivs_den] in H. unfold page_in_ranges in H. rewrite existsb_app in H. apply orb_prop in H as [H|H].
    - exists s. split; [left; reflexivity|]. unfold siv_den in H.
      destruct (lden E (fst s) <? lden E (snd s)) eqn:C; [|cbn in H; discriminate]. apply Z.ltb_lt in C.
      cbn [existsb fst snd] in H. rewrite orb_false_r in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      pose proof (u64_range p). unfold page_size in H2.
      rewrite !u_of_Z in H1, H2 by lia. rewrite u_of_Z in H2 by lia. lia.
    - destruct (IH p WF H) as [s2 [A B]]. exists s2. split; [right; exact A | exact B].
  Qed.

  Lemma in_all_pages_zz : forall S p xz, zz_ok S -> zin xz S = true -> 0 <= xz < 2 ^ 64 ->
    bv_unsigned p = xz / 4096 * 4096 -> In p (all_pages (zz2ww S)).
  Proof.
    intros S p xz HS Hz Hr Hp. apply (window_page_in_all_pages (zz2ww S) (Z_to_bv 64 xz) p).
    - rewrite in_rangesb_zz by exact HS. rewrite u_of_Z by lia. exact Hz.
    - rewrite u_of_Z by lia. unfold page_size. exact Hp.
  Qed.

  Lemma vis_entry : forall q, In q (a_vis ch ++ a_ghost ch) ->
    In (lin_of (fst q), lin_of (snd q)) (DG_visg g)
    /\ uE E (fst q) = lden E (lin_of (fst q)) /\ uE E (snd q) = lden E (lin_of (snd q))
    /\ In (uE E (fst q), uE E (snd q)) (VISZ sp0z brk0z X).
  Proof.
    intros q Hq. destruct lzc_parts as (_ & _ & _ & _ & NW & GH).
    pose proof (proj1 (forallb_forall _ _) NW q Hq) as H1. apply andb_prop in H1 as [H1 H2]. rewrite lin_nowrapRB_eqf in H1, H2.
    pose proof (lin_nowrapR_sound _ _ _ _ _ KN H1) as U1. pose proof (lin_nowrapR_sound _ _ _ _ _ KN H2) as U2.
    assert (HD : In (lin_of (fst q), lin_of (snd q)) (DG_visg g)).
    { unfold DG_visg. rewrite <- (f_equal dg_vis D : map _ (a_vis ch) = DG_vis g).
      apply in_app_iff in Hq as [Hq|Hq].
      - apply in_app_iff. left. apply (in_map (fun p : expr * expr => (lin_of (fst p), lin_of (snd p))) _ _ Hq).
      - apply in_app_iff. right. rewrite GH in Hq. destruct Hq as [<-|[]]. left. vm_compute. reflexivity. }
    split; [exact HD|]. split; [exact U1|]. split; [exact U2|].
    destruct VISZ0_eq as [V1 V2]. unfold VISZ. rewrite <- V1, <- V2, <- map_app.
    apply (in_map (fun p : expr * expr => (uE E (fst p), uE E (snd p))) _ _ Hq).
  Qed.

  Ltac keep_rel := match goal with |- context [vE E ?k] => repeat match goal with H : ?T |- _ => lazymatch T with context [vE E k] => fail | _ => clear H end end end.
  Ltac rlia := first [solve [keep_rel; lia] | lia].
  Lemma DG_visg_len : forall e, In e (DG_visg g) -> 4096 <= lden E (snd e) /\ lden E (fst e) mod 4096 = 0 /\ (lden E (fst e) + lden E (snd e)) mod 4096 = 0.
  Proof.
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP).
    intros e He. clearbody D LZC. unfold DG_visg in He. cbn [DG_vis app] in He.
    destruct g;
    repeat (destruct He as [<-|He]; [unfold pg, pgo, lRI, lden; cbn [fst snd tden]; rewrite ?uE_var; rlia|]); destruct He.
  Qed.

  Lemma zz_ok_S : zz_ok (PM_S sp0z brk0z X).
  Proof.
    prep. zlists. clearbody D LZC. unfold zz_ok.
    destruct g; cbn [map app fst snd]; [|apply Forall_inv in Bg; cbn [fst snd] in Bg];
      repeat constructor; cbn [fst snd]; unfold SHOFF; unfold brk0z in *; rlia.
  Qed.

  Lemma lazy_sym : m_vm_lazy model = sivs_den E (DG_lazy g) /\ vm_noaccess (m_vmmaps model) = sivs_den E (DG_noacc g)
                   /\ Forall (siv_wf E) (DG_lazy g) /\ Forall (siv_wf E) (DG_noacc g).
  Proof.
    pose proof (f_equal dg_ledgers D : cs_ledgers ch = Some (DG_noacc g, DG_lazy g)) as Dled.
    destruct (cs_ledgers_sound _ _ _ _ _ _ _ _ _ _ _ _ _ HC Dled) as (A & B & WN & WL). repeat split; assumption.
  Qed.

  Ltac inAPPS := unfold APPS; apply (in_map asiv); cbn [firstn skipn DG_vis app In]; repeat (first [left; reflexivity | right]).

  Lemma incl_materialized : incl (m_vm_materialized model) (all_pages (zz2ww (PM_S sp0z brk0z X))).
  Proof.
    pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP).
    destruct lazy_sym as (LZ & _ & WL & _). destruct lzc_parts as (_ & CD & _).
    pose proof (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) as MI.
    intros p Hp.
    pose proof (minv_aligned _ _ MI p Hp) as Hal. unfold page_size in Hal.
    pose proof (minv_allowed _ _ MI p Hp) as HA. pose proof (minv_lazy _ _ MI p Hp) as HL.
    rewrite LZ in HL. apply page_in_sivs in HL as [s [Hs HL]]; [|exact WL].
    unfold allowA in HA. apply page_allowedb_flat_map in HA as [q [Hq HA]].
    destruct (vis_entry q Hq) as (Hin & Ua & Un & HV). destruct (DG_visg_len _ Hin) as (Hn & Hala & Haln).
    cbn [fst snd] in Hn, Hala, Haln. rewrite <- Ua in Hala, Haln. rewrite <- Un in Hn, Haln.
    pose proof (u64_range p) as Hup. pose proof (u64_range (edenot E (fst q)) : 0 <= uE E (fst q) < _) as Hua.
    set (up := bv_unsigned p) in *. set (a := uE E (fst q)) in *. set (n := uE E (snd q)) in *.
    apply page_allowedb_In in HA as [iv [Hiv HI]]. fold up in HI.
    unfold allow1 in Hiv. cbn [In] in Hiv. unfold sh_lo, sh_hi in Hiv. cbn [fst snd] in Hiv.
    replace (shadow_off ASAN_H) with SHOFF in Hiv by reflexivity. fold a in Hiv. fold n in Hiv.
    destruct Hiv as [<- | [<- | []]]; cbn [fst snd] in HI; unfold pagedown, pageup in HI.
    -
      cbn [DG_lazy In] in Hs.
      assert (CASEB22 : lden E (pg (K_B22 g)) <= up /\ up + 4096 <= lden E (pgo 8388608 (K_B22 g)) -> In p (all_pages (zz2ww (PM_S sp0z brk0z X)))).
      { intros [H1 H2]. apply (in_all_pages_zz _ p up zz_ok_S); [|lia|lia].
        unfold PM_S. unfold zin. cbn [existsb fst snd]. unfold X, Xof. cbn [ps_b22].
        unfold pg, pgo, lden in H1, H2. cbn [fst snd tden] in H1, H2. rewrite ?uE_var in H1, H2.
        apply orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      destruct Hs as [<- | Hs]; [apply CASEB22; exact HL|].

      unfold DG_visg in Hin. cbn [DG_vis app In] in Hin.
      assert (DISJ : In (asiv (lin_of (fst q), lin_of (snd q))) (APPS g) -> False).
      { intros HinA. pose proof (cross_disjB_sound _ _ _ _ KN _ _ CD _ _ HinA Hs) as X1.
        unfold asiv in X1. cbn [fst snd] in X1. rewrite lcat_den in X1. rewrite <- Ua, <- Un in X1. lia. }
      assert (HIa : a <= up /\ up + 4096 <= a + n) by lia.
      destruct Hin as [E1|[E3|Hin]].
      + exfalso. apply DISJ. rewrite <- E1. inAPPS.
      + apply CASEB22. injection E3 as E3a E3b. rewrite <- E3a in Ua. rewrite <- E3b in Un.
        unfold lden in Un. cbn [fst snd tden] in Un. rewrite Ua in HIa. unfold pgo, pg, lden in *. cbn [fst snd tden] in *. lia.
      + exfalso. apply DISJ.
        repeat (destruct Hin as [EQ|Hin]; [rewrite <- EQ; inAPPS|]). all: try destruct Hin.
    -
      apply (in_all_pages_zz _ p (Z.max up (SHOFF + a / 8)) zz_ok_S); [| unfold SHOFF; lia | lia].
      apply zin_spec. exists (SW a n). split.
      + unfold PM_S. right. apply (in_map (fun p0 : Z * Z => SW (fst p0) (snd p0)) _ _ HV).
      + unfold SW. cbn [fst snd]. unfold SHOFF in *. lia.
  Qed.

  Fixpoint zinP (z : Z) (l : list (Z * Z)) : Prop :=
    match l with [] => False | p :: r => (fst p <= z < fst p + snd p) \/ zinP z r end.
  Lemma zin_iff : forall z l, zin z l = true <-> zinP z l.
  Proof.
    intros z l. induction l as [|p l IH]; cbn [zin zinP existsb].
    - split; [discriminate | tauto].
    - unfold zin in IH. rewrite orb_true_iff, IH, andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
  Qed.
  Lemma zinP_app : forall z l1 l2, zinP z (l1 ++ l2) <-> zinP z l1 \/ zinP z l2.
  Proof. intros z l1 l2. induction l1 as [|p l1 IH]; cbn [zinP app]; tauto. Qed.

  Lemma PM_maps_eq : vm_maps (m_vmmaps model) = zz2ww (PM_MAPS brk0z X).
  Proof. exact (pm_maps _ _ _ _ _ (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)). Qed.
  Lemma PM_lazy_eq : m_vm_lazy model = zz2ww (PM_LAZY sp0z X).
  Proof. exact (pm_lazy _ _ _ _ _ (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)). Qed.
  Lemma PM_noacc_eq : vm_noaccess (m_vmmaps model) = zz2ww (PM_NOACC brk0z X).
  Proof. exact (pm_noacc _ _ _ _ _ (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)). Qed.

  Lemma zz_ok_maps : zz_ok (PM_MAPS brk0z X).
  Proof. prep. zlists. clearbody D LZC. unfold zz_ok. solve_forall; cbn [fst snd]; destruct g; try (apply Forall_inv in Bg; cbn [fst snd] in Bg); unfold brk0z in *; lia. Qed.
  Lemma zz_ok_noacc : zz_ok (PM_NOACC brk0z X).
  Proof. prep. zlists. clearbody D LZC. unfold zz_ok. solve_forall; cbn [fst snd]; destruct g; try (apply Forall_inv in Bg; cbn [fst snd] in Bg); unfold brk0z in *; lia. Qed.
  Lemma zz_ok_zr : zz_ok (PM_ZR sp0z X).
  Proof. prep. zlists. clearbody D LZC. unfold zz_ok. solve_forall; cbn [fst snd]; lia. Qed.

  Lemma lazy_ranges_ok : lazy_ranges_okb ASEGS (zz2ww (PM_LAZY sp0z X)) = true.
  Proof.
    pose proof (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) as LB. rewrite PM_lazy_eq in LB.
    pose proof facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TOPm & _ & _ & _ & VSP).
    unfold lazy_ranges_okb. apply andb_true_intro. split; [vm_compute; reflexivity|].
    apply forallb_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) LB r Hr) as [H1 H2].
    replace (img_hi ASAN_H) with 7241728 in H1 by reflexivity. replace (img_lo ASAN_H) with 65536 in H1 by reflexivity. rewrite TOPm in H2.
    unfold lazy_range_okb. apply andb_true_intro. split.
    - unfold range_nowrapb. apply Z.leb_le. lia.
    - unfold ASEGS. cbn -[Z.leb Z.add bv_unsigned]. unfold seg_disjoint_rangeb.
      cbn [seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003 Z.of_N].
      rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le. pose proof (u64_range (snd r)). repeat split; try reflexivity; lia.
  Qed.

  Fixpoint sumw (l : list (Z * Z)) : Z := match l with [] => 0 | p :: r => snd p / 4096 + 2 + sumw r end.
  Fixpoint sumb (l : list (Z * Z)) : Z := match l with [] => 0 | p :: r => snd p / 32768 + 3 + sumb r end.
  Lemma wbudget_zz : forall l, zz_ok l -> wbudget (zz2ww l) = sumw l.
  Proof.
    induction l as [|[a n] l IH]; intros Hok; [reflexivity|]. apply Forall_cons_iff in Hok as [[H1 H2] Hok]. cbn [fst snd] in *.
    unfold zz2ww. cbn [map wbudget sumw fst snd]. fold (zz2ww l). rewrite (IH Hok). rewrite u_of_Z by lia. unfold page_size. reflexivity.
  Qed.
  Lemma SW_pages : forall a n, 0 <= a -> 0 <= n -> snd (SW a n) / 4096 + 2 <= n / 32768 + 3.
  Proof. intros a n Ha Hn. unfold SW. cbn [snd]. lia. Qed.
  Lemma sumw_SW : forall V, Forall (fun p => 0 <= fst p /\ 0 <= snd p) V -> sumw (map (fun p => SW (fst p) (snd p)) V) <= sumb V.
  Proof.
    induction V as [|[a n] V IH]; intros HV; [cbn; lia|]. apply Forall_cons_iff in HV as [[Ha Hn] HV]. cbn [fst snd] in Ha, Hn.
    cbn [map sumw sumb fst snd]. pose proof (SW_pages a n Ha Hn). specialize (IH HV). cbn [fst snd] in *. lia.
  Qed.
  Lemma pages_S : pages_total (zz2ww (PM_S sp0z brk0z X)) <= PM_S_PAGES.
  Proof.
    eapply Z.le_trans; [apply pages_total_le_wbudget|]. rewrite (wbudget_zz _ zz_ok_S).
    unfold PM_S. cbn [sumw snd].
    assert (HV : Forall (fun p => 0 <= fst p /\ 0 <= snd p) (VISZ sp0z brk0z X)).
    { prep. zlists. clearbody D LZC. solve_forall; cbn [fst snd]; try lia. destruct g; [|apply Forall_inv in Bg]; cbn [fst snd] in *; unfold brk0z; lia. }
    pose proof (sumw_SW _ HV) as HS.
    assert (HB : sumb (VISZ sp0z brk0z X) <= 66835).
    { pose proof facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PGD & _ & _ & VSP).
      unfold VISZ, VISZ0. clearbody D LZC. clear -PGD VSP. unfold page_down in *. destruct (ps_granted X); cbn -[Z.add Z.mul Z.div Z.le Z.sub]; lia. }
    unfold PM_S_PAGES. lia.
  Qed.

  Lemma zinP_ifr : forall z a b, zinP z (if a <? b then [(a, b - a)] else []) <-> a <= z < b.
  Proof. intros z a b. destruct (a <? b) eqn:C; [apply Z.ltb_lt in C | apply Z.ltb_ge in C]; cbn [zinP fst snd]; lia. Qed.
  Ltac zinP_norm2 := cbn [zinP fst snd app]; repeat (rewrite ?zinP_app, ?zinP_ifr; cbn [zinP fst snd app]).

  Ltac lia_leaf := lazymatch goal with |- _ \/ _ => fail | |- _ => lia end.
  Ltac solve_disj := first [ lia_leaf | (left; solve_disj) | (right; solve_disj) ].
  Ltac zsolve := repeat match goal with H : _ \/ _ |- _ => destruct H | H : False |- _ => destruct H end; solve_disj.
  Ltac lia_leafT := lazymatch goal with |- _ \/ _ => fail | |- _ => solve [fastlia] end.
  Ltac solve_disjT := first [ lia_leafT | (left; solve_disjT) | (right; solve_disjT) ].
  Ltac zsolveT := repeat match goal with H : _ \/ _ |- _ => destruct H | H : False |- _ => destruct H end; first [solve_disjT | solve_disj].
  Fixpoint zpinP (z : Z) (l : list (Z * Z)) : Prop :=
    match l with [] => False | p :: r => (fst p <= z /\ z + 4096 <= fst p + snd p) \/ zpinP z r end.
  Lemma zpin_iff : forall z l, zpin z l = true <-> zpinP z l.
  Proof.
    intros z l. induction l as [|p l IH]; cbn [zpin zpinP existsb].
    - split; [discriminate | tauto].
    - unfold zpin in IH. rewrite orb_true_iff, IH, andb_true_iff, !Z.leb_le. tauto.
  Qed.
  Lemma zpinP_app : forall z l1 l2, zpinP z (l1 ++ l2) <-> zpinP z l1 \/ zpinP z l2.
  Proof. intros z l1 l2. induction l1 as [|p l1 IH]; cbn [zpinP app]; tauto. Qed.
  Lemma zpinP_ifr : forall z a b, zpinP z (if a <? b then [(a, b - a)] else []) <-> (a <= z /\ z + 4096 <= b).
  Proof. intros z a b. destruct (a <? b) eqn:C; [apply Z.ltb_lt in C | apply Z.ltb_ge in C]; cbn [zpinP fst snd]; lia. Qed.
  Ltac zpinP_norm := cbn [zpinP fst snd app]; repeat (rewrite ?zpinP_app, ?zpinP_ifr; cbn [zpinP fst snd app]).

  Lemma rsub_zz : forall A B, zz_ok A -> zz_ok B -> (forall z, 0 <= z < 2 ^ 64 -> zinP z A -> zinP z B) -> rsub (zz2ww A) (zz2ww B).
  Proof.
    intros A B HA HB H x Hx. rewrite in_rangesb_zz in Hx by exact HA. rewrite in_rangesb_zz by exact HB.
    apply zin_iff. apply H; [exact (u64_range x)|]. apply zin_iff. exact Hx.
  Qed.

  Lemma Z0_noS0_cases : forall z, zinP z (PM_ZR sp0z X) -> ~ zinP z (PM_S sp0z brk0z X) ->
    ((2201439137792 <= z < 17594333495296) \/ (2147446784 <= z < 2415882240))
    /\ exists y, In y (LZS g cls) /\ lden E (fst y) <= z < lden E (snd y).
  Proof.
    intros z HZ HS. prep.
    assert (NB : ~ (4096 * vE E (K_B22 g) <= z < 4096 * vE E (K_B22 g) + 0x800000)).
    { intros Hb. apply HS. unfold PM_S. cbn [zinP fst snd]. left. unfold X, Xof. cbn [ps_b22]. exact Hb. }
    revert HZ. zlists. zinP_norm2. intros HZ.
    split; [zsolve|].
    unfold LZS. cbn [DG_lazy tl].
    destruct HZ as [HZ|[HZ|[HZ|[]]]].
    - exfalso. exact (NB HZ).
    - exists ((2201439137792, []), (17594333495296, [])). split; [cbn; tauto|]. unfold lden; cbn [fst snd tden]; lia.
    - exists ((2147446784, []), (2415882240, [])). split; [cbn; tauto|]. unfold lden; cbn [fst snd tden]; lia.
  Qed.

  Tactic Notation "pick" integer(n) := do n right; left.
  Lemma ZL_Z : forall z, zinP z (PM_ZR sp0z X) -> zinP z (PM_LAZY sp0z X).
  Proof.
    intros z. prep. zlists. clearbody D LZC. zinP_norm2. intros HZ.
    destruct HZ as [Hz|[Hz|[Hz|[]]]]; [pick 0|pick 4|pick 6]; lia.
  Qed.
  Lemma LM_Z : forall z, zinP z (PM_LAZY sp0z X) -> zinP z (PM_MAPS brk0z X).
  Proof.
    intros z. prep. zlists. clearbody D LZC. zinP_norm2. intros HZ.
    destruct HZ as [Hz|[Hz|[Hz|[Hz|[Hz|[Hz|[Hz|[]]]]]]]];
      [pick 1|pick 10|pick 11|pick 11|pick 14|pick 15|pick 16]; cbn [fst snd]; lia.
  Qed.
  Lemma lazy_page_Z : forall z,
    ((2201439137792 <= z < 17594333495296) \/ (2147446784 <= z < 2415882240)) ->
    zpinP (z / 4096 * 4096) (PM_LAZY sp0z X).
  Proof.
    intros z Hz. pose proof facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP).
    revert Hz. zlists. intros Hz. zpinP_norm.
    clearbody D LZC. elim_div z 4096.
    destruct Hz as [Hz|Hz]; [pick 4 | pick 6]; lia.
  Qed.

  Lemma bands_noacc :
    (4096 * vE E K_B06 + 137439023104 <= 2147446784 \/ 17594333495296 <= 4096 * vE E K_B06)
    /\ (4096 * vE E K_B08 + 8388608 <= 2147446784 \/ 17594333495296 <= 4096 * vE E K_B08)
    /\ (g = false -> 4096 * vE E K_META + 8192 <= 2147446784 \/ 17594333495296 <= 4096 * vE E K_META).
  Proof.
    split; [|split].
    - exact (proj2 (KBAND_in (ps_b06 X, 137439023104) ltac:(left; unfold pm_kernel_placed; apply in_app_iff; left; cbn [In]; tauto))).
    - exact (proj2 (KBAND_in (ps_b08 X, 8388608) ltac:(left; unfold pm_kernel_placed; apply in_app_iff; left; cbn [In]; tauto))).
    - intros Hg. pose proof (fun HI => proj2 (KBAND_in (ps_b19r X, 8192) HI)) as K. unfold X, Xof in K. cbn [ps_b19r ps_granted fst snd] in K.
      unfold pm_kernel_placed in K. cbn [ps_granted Xof] in K. rewrite Hg in K. apply K. left. apply in_app_iff. right. left. reflexivity.
  Qed.
  Lemma noacc_Z : forall z,
    ((2201439137792 <= z < 17594333495296) \/ (2147446784 <= z < 2415882240)) ->
    ~ zinP z (PM_NOACC brk0z X).
  Proof.
    intros z Hz. prep. pose proof (pso_brk _ _ _ _ pm_syms_ok_open) as PB. unfold X, Xof in PB. cbn [ps_granted] in PB.
    pose proof bands_noacc as (N06 & N08 & Nmeta).
    revert Hz. zlists. clearbody D LZC. intros Hz. zinP_norm2.
    destruct g; [destruct (PB eq_refl) as [PB1 _]; unfold ALOWSH_LO in PB1; clear Nmeta | specialize (Nmeta eq_refl); apply Forall_inv in Bg; cbn [fst snd] in Bg];
      cbn [fst snd]; unfold brk0z in *; intros HN; zsolveT.
  Qed.

  Lemma rsub_ZL : rsub (zz2ww (PM_ZR sp0z X)) (zz2ww (PM_LAZY sp0z X)).
  Proof. apply (rsub_zz _ _ zz_ok_zr zz_ok_lazy). intros z _. apply ZL_Z. Qed.
  Lemma rsub_LM : rsub (zz2ww (PM_LAZY sp0z X)) (vm_maps (m_vmmaps model)).
  Proof. rewrite PM_maps_eq. apply (rsub_zz _ _ zz_ok_lazy zz_ok_maps). intros z _. apply LM_Z. Qed.
  Lemma ZR_b22 : forall z, 4096 * vE E (K_B22 g) <= z < 4096 * vE E (K_B22 g) + 0x800000 -> zinP z (PM_ZR sp0z X).
  Proof. intros z Hz. unfold PM_ZR, X, Xof. cbn [zinP app fst snd ps_b22]. left. exact Hz. Qed.
  Lemma ZR_high : forall z, 2201439137792 <= z < 17594333495296 -> zinP z (PM_ZR sp0z X).
  Proof.
    intros z Hz. unfold PM_ZR. zinP_norm2. pick 1. lia.
  Qed.
  Lemma ZR_low : forall z, 2147446784 <= z < 2415882240 -> zinP z (PM_ZR sp0z X).
  Proof. intros z Hz. unfold PM_ZR. zinP_norm2. pick 2. lia. Qed.

  Lemma VISZ_facts : Forall (fun p =>
      (4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608 /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p) /\ 0 < snd p)
      \/ p = (65536, 6844416) \/ p = (page_down sp0z - 8388608, 140737496743936 - page_down sp0z)) (VISZ sp0z brk0z X).
  Proof.
    prep. pose proof (pso_brk _ _ _ _ pm_syms_ok_open) as PB. unfold X, Xof in PB. cbn [ps_granted] in PB.
    pose proof bands_noacc as (N06 & _ & Nmeta).
    assert (KBp : forall p, In p (pm_kernel_placed X) \/ p = (ps_b13 X, 4096) ->
              4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608 /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p) /\ 0 < snd p).
    { intros p Hp. pose proof (KBAND_in p Hp) as [_ HB]. pose proof KB as [K1 K2]. cbv zeta in K1.
      destruct Hp as [Hp| ->].
      - pose proof (proj1 (Forall_forall _ _) K1 p Hp) as [K3 K4]. pose proof (proj1 (Forall_forall _ _) KPS_len p Hp) as [_ K5]. repeat split; assumption.
      - cbn [fst snd] in *. repeat split; try assumption; lia. }
    destruct lzc_parts as (_ & _ & _ & G5 & _).
    assert (BRK5 : g = true -> 7241728 <= brk0z /\ brk0z + 12288 <= 2147446784).
    { intros Hg. specialize (G5 Hg). pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ G5) as R5. rewrite uE_var in R5.
      destruct (PB Hg) as [PB1 _]. unfold ALOWSH_LO in PB1. unfold brk0z in *. lia. }
    unfold VISZ, VISZ0. rewrite (RI_lin X (4096 * vE E K_B06) (vE E K_R06) eq_refl REL).
    Ltac kb KBp := left; refine (KBp _ _); unfold pm_kernel_placed, X, Xof;
                   cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted In app];
                   clear; destruct (hole_granted h); cbn [app In]; tauto.
    repeat apply Forall_cons; try apply Forall_nil;
      first [ kb KBp
            |   unfold X, Xof; cbn [ps_granted ps_b19r]; clearbody D LZC; destruct g;
                [ specialize (BRK5 eq_refl); left; cbn [fst snd]; lia
                | specialize (Nmeta eq_refl); apply Forall_inv in Bg; cbn [fst snd] in Bg; left; cbn [fst snd]; lia ]
            |   left; unfold X, Xof; cbn [fst snd ps_b06]; clearbody D LZC; lia
            |   right; left; reflexivity
            |   right; right; reflexivity ].
  Qed.

  Lemma SW_ZR : forall a n z, 4096 <= a -> a + n <= page_down sp0z - 8388608 -> (a + n <= 2147446784 \/ 17594333495296 <= a) -> 0 < n ->
    fst (SW a n) <= z < fst (SW a n) + snd (SW a n) -> zinP z (PM_ZR sp0z X).
  Proof.
    intros a n z Ha Hn Hb Hn0 Hz. unfold SW, SHOFF in Hz. cbn [fst snd] in Hz.
    pose proof facts as (_ & _ & _ & _ & V0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PGD & V6' & _ & VSP).
    clearbody D LZC. destruct Hb as [Hb|Hb]; [apply ZR_low; lia | apply ZR_high; lia].
  Qed.

  Lemma zinP_map_SW : forall z l, zinP z (map (fun p => SW (fst p) (snd p)) l) -> exists p, In p l /\ fst (SW (fst p) (snd p)) <= z < fst (SW (fst p) (snd p)) + snd (SW (fst p) (snd p)).
  Proof.
    intros z l. induction l as [|p l IH]; cbn [map zinP]; [tauto|].
    intros [Hz|Hz]; [exists p; split; [left; reflexivity | exact Hz]|]. destruct (IH Hz) as [q [Hq Hzq]]. exists q. split; [right; exact Hq | exact Hzq].
  Qed.

  Lemma rsub_SZ : rsub (zz2ww (PM_S sp0z brk0z X)) (zz2ww (PM_ZR sp0z X)).
  Proof.
    apply (rsub_zz _ _ zz_ok_S zz_ok_zr). intros z Hz HZ.
    pose proof facts as (_ & _ & _ & _ & V0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PGD & V6' & _ & VSP).
    unfold PM_S in HZ. cbn [zinP] in HZ. destruct HZ as [HZ|HZ].
    { apply ZR_b22. unfold X, Xof in HZ. cbn [fst snd ps_b22] in HZ. exact HZ. }
    apply zinP_map_SW in HZ as [p [Hp Hzp]].
    pose proof (proj1 (Forall_forall _ _) VISZ_facts p Hp) as [(H1 & H2 & H3 & H4) | [-> | ->]].
    - exact (SW_ZR _ _ _ H1 H2 H3 H4 Hzp).
    - apply ZR_low. unfold SW, SHOFF in Hzp. cbn [fst snd] in Hzp. lia.
    - apply ZR_high. unfold SW, SHOFF in Hzp. cbn [fst snd] in Hzp. clearbody D LZC. lia.
  Qed.

  Lemma hidden_zero : hidden_zero_on (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) (zz2ww (PM_ZR sp0z X)) (mkst R (Z_to_bv 64 A_MAIN) FULL (seg_rom ASEGS)).
  Proof.
    intros a HID HZR. cbn [ms_mem mkst]. prep.
    unfold hiddenb in HID. apply andb_prop in HID as [HL HS]. apply negb_true_iff in HS.
    rewrite in_rangesb_zz in HL by exact zz_ok_lazy. rewrite in_rangesb_zz in HS by exact zz_ok_S. rewrite in_rangesb_zz in HZR by exact zz_ok_zr.
    apply zin_iff in HL. apply zin_iff in HZR.
    assert (HSn : ~ zinP (bv_unsigned a) (PM_S sp0z brk0z X)) by (intros Hc; apply zin_iff in Hc; congruence).
    destruct (Z0_noS0_cases _ HZR HSn) as [HZ4 [y [Hy Hyb]]].
    pose proof (u64_range a) as Hua. set (ua := bv_unsigned a) in *.
    assert (HuK : 2147446784 <= ua < 17594333495296) by (clearbody D LZC; lia).
    pose proof VISZ_facts as VF. pose proof (KBAND_in _ (or_intror eq_refl)) as [_ B13b]. unfold X, Xof in B13b. cbn [fst snd ps_b13] in B13b.
    apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC a).
    -
      unfold hid. apply orb_true_intro. right. apply negb_true_iff. unfold vis. fold ua.
      replace (in_hull ASAN_H ua) with false by (symmetry; unfold in_hull; apply andb_false_iff; right; apply Z.ltb_ge; change (img_hi ASAN_H) with 7241728; lia).
      replace (TOP model <=? ua) with false by (symmetry; apply Z.leb_gt; rewrite TOPm; clearbody D LZC; lia).
      cbn [orb]. apply andb_false_iff. right. apply orb_false_iff. split.
      + apply negb_false_iff. rewrite PM_lazy_eq, page_in_ranges_zz by exact zz_ok_lazy. apply zpin_iff.
        unfold page_base, page_base_of. fold ua. unfold page_size. rewrite u_of_Z by lia. apply lazy_page_Z. exact HZ4.
      + unfold in_allow. apply orb_false_iff. split.
        * destruct (in_vis E ch ua) eqn:IV; [exfalso|reflexivity]. unfold in_vis in IV. apply existsb_exists in IV as [q [Hq Hb]].
          apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
          destruct (vis_entry q ltac:(apply in_app_iff; left; exact Hq)) as (_ & _ & _ & HV).
          pose proof (proj1 (Forall_forall _ _) VF _ HV) as VF1. cbn [fst snd] in VF1. clearbody D LZC.
          destruct VF1 as [(F1 & F2 & F3 & F4) | [F | F]]; [lia | |]; injection F as F1 F2; lia.
        * destruct (in_sh ASAN_H E ch ua) eqn:IS; [exfalso|reflexivity]. unfold in_sh in IS. apply existsb_exists in IS as [q [Hq Hb]].
          apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2. unfold sh_lo, sh_hi in Hb1, Hb2. cbn [fst snd] in Hb1, Hb2.
          replace (shadow_off ASAN_H) with SHOFF in Hb1, Hb2 by reflexivity.
          destruct (vis_entry q ltac:(apply in_app_iff; left; exact Hq)) as (_ & _ & _ & HV).
          apply HSn. unfold PM_S. cbn [zinP]. right.
          clear -HV Hb1 Hb2. induction (VISZ sp0z brk0z X) as [|w V IH]; [destruct HV|]. cbn [map zinP]. destruct HV as [->|HV]; [left | right; exact (IH HV)].
          unfold SW. cbn [fst snd]. lia.
    - fold ua. rewrite PM_maps_eq, in_ivs_zz by exact zz_ok_maps. apply zin_iff. apply LM_Z. exact HL.
    - fold ua. rewrite PM_noacc_eq, in_ivs_zz by exact zz_ok_noacc. destruct (zin ua (PM_NOACC brk0z X)) eqn:NA; [|reflexivity]. exfalso. apply zin_iff in NA. exact (noacc_Z _ HZ4 NA).
    - rewrite PM_lazy_eq, page_in_ranges_zz by exact zz_ok_lazy. apply zpin_iff.
      unfold page_base, page_base_of. fold ua. unfold page_size. rewrite u_of_Z by lia. apply lazy_page_Z. exact HZ4.
    - fold ua. destruct lzc_parts as (_ & _ & _ & _ & NW & GH). unfold in_ghost. rewrite GH. cbn [existsb fst snd]. rewrite orb_false_r.
      destruct (vis_entry (EMd Instr.M_MUL (ELit 4096) (EVar K_B13), ELit 4096) ltac:(apply in_app_iff; right; rewrite GH; left; reflexivity)) as (_ & Ua & Un & _).
      cbn [fst snd] in Ua, Un. rewrite Ua, Un.
      replace (lin_of (EMd Instr.M_MUL (ELit 4096) (EVar K_B13))) with (pg K_B13) by (vm_compute; reflexivity).
      replace (lden E (lin_of (ELit 4096))) with 4096 by (vm_compute; reflexivity).
      unfold pg, lden. cbn [fst snd tden]. rewrite uE_var. clearbody D LZC.
      apply andb_false_iff. destruct (Z.le_gt_cases (4096 * vE E K_B13 + 4096) 2147446784); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  Qed.

  Theorem lzok_open :
    lzok ASEGS (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) (zz2ww (PM_ZR sp0z X)) (cfg_of ASEGS R A_MAIN FULL model)
    /\ pages_total (zz2ww (PM_S sp0z brk0z X)) <= PM_S_PAGES.
  Proof.
    split; [|exact pages_S].
    pose proof (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as PMo.
    constructor; cbn [cfg_model cfg_ms cfg_of].
    - exact lazy_ranges_ok.
    - constructor.
      + exact PM_lazy_eq.
      + exact (minv_nodup _ _ (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)).
      + exact incl_materialized.
      + pose proof (pm_eager _ _ _ _ _ PMo) as EG. cbn [cfg_model cfg_of] in EG. change (BothAcct.eager_used model) with (eager_used model) in EG.
        pose proof (pm_limit _ _ _ _ _ PMo) as LIM. cbn [cfg_model cfg_of] in LIM. rewrite LIM.
        pose proof pages_S as PS. unfold PM_S_PAGES in PS. unfold target_alloc_limit, page_size. lia.
    - exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact hidden_zero.
    - exact rsub_SZ.
    - exact rsub_ZL.
    - exact rsub_LM.
  Qed.
End LZ.

Section PMB.
  Variables (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config).
  Hypothesis P : P_main sp0 brk0 mbase rdraw inp c.

End PMB.
