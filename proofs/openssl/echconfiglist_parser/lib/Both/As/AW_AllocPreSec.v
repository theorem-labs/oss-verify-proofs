(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition alloc_pre_sec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size needed TSD CTX TH sb SO : Z) (T : list Z) (rest : list word) : machine_state -> Prop :=
  fun ms' => exists (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) m' (j8 : list byte),
    ms' = MS (mkR (wz 0x19709c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 0) (wz size) (wz AINST) (wz (TH + 208)) (wz needed) (wz 8) x14 x15 x16 x17
                  (wz 8) (wz needed) (wz 2048) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
             F (Z_to_bv 64 0x19b65c) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ AENV tp TSD CTX TH sb SO T rest m' /\ aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m' j8 /\ stk asegs m' lo (bv_unsigned sp + -128).
End HCW.

Section AllocPreSec.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size needed SO : Z) (T : list Z) (rest : list word) (TSD CTX TH sb : Z).
  Hypothesis DNEED : hidden (needed = round_up (Z.max size 8) 8 + 4096).
  Let Wpre : list ivl := [(lo, bv_unsigned sp)]%Z.
  Let PREPOST := alloc_pre_sec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed TSD CTX TH sb SO T rest.
  Let AFR := aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 352 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).

  Ltac prep :=
    pose proof DNEED as D; destruct D as [DN];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328)
      by (clear - LO RNG SBR TPR SOR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct TPR as [TPR']; destruct SOR as [SOR'];
          unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *; acb; change (2^47)%Z with 140737488355328%Z in SOR'; lia);
        region_sides; name_bands;
    assert (GEO : size + 8 <= needed - 4088 /\ needed <= size + 4096 + 8 /\ exists nk, needed - 4096 = 8 * nk)
      by (clear - DN SZ; try acb; subst needed; unfold round_up; split; [|split]; try (Z.div_mod_to_equations; lia); exists ((Z.max size 8 + 8 - 1) / 8); Z.div_mod_to_equations; lia);
    destruct GEO as (G1 & G2 & [nk NK]);
    assert (ALN : exists thq, TH = 16 * thq) by (clear - RNG; try acb; destruct RNG as [RNG']; exists (TH / 16); Z.div_mod_to_equations; aunf; lia);
    destruct ALN as (thq & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (RZ7 : rz_log size = 7) by (unfold rz_log; repeat match goal with |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_gt a b)) by lia] end; reflexivity).

  (* [comment removed for export] *)
  Lemma aenv_now_pre_sec : forall m0 m1, AENV tp TSD CTX TH sb SO T rest m0 -> munch Wpre m0 m1 -> wmono asegs m0 m1 -> AENV tp TSD CTX TH sb SO T rest m1.
  Proof.
    intros m0 m1 E MU WM. unfold Wpre in MU. prep. open_env E. region_table.
    lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    econstructor; unfold AGOT_VALS; cbn [map repeat];
      first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]
            | eapply u64arr_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; region_decide] ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partC_pre_sec : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch Wpre m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    evt asegs PREPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 8) (wz 0) (wz (Z.max size 8)) (wz 8) x12 x13 x14 x15 x16 x17
               (wz 8) (wz 7) (wz 0x10000) (wz size) (wz AINST) (wz SO) (wz 0xffff) (wz 7) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196fb0) fc None mB (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI MU WM FR ST.
    pose proof (munch_refl Wpre mB) as MUB. pose proof (wmono_refl asegs mB) as WMB. unfold Wpre in MUB.
    unfold Wpre in MU. prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST.
    assert (MX : 8 <= Z.max size 8 /\ size <= Z.max size 8 /\ Z.max size 8 <= needed - 4096) by (clear - SZ G1 G2; try acb; lia).
    remember (Z.max size 8) as mx eqn:EMX in MX |- *. assert (MXh : hidden (mx = Z.max size 8)) by (constructor; exact EMX). clear EMX.
    region_table.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709551608 + ?y)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709551608 + y)) with (Z_to_bv 64 (needed - 4096)) end.
    2:{ f_equal. replace (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 8) 9) + -1))) 8) with 0 by (vm_compute; reflexivity).
        rewrite (unsigned_lit (mx + 7)) by lia. change 18446744073709551608 with (2^64 - 2^3)%Z. rewrite StrFun.land_align_down by lia.
        unhide_hyp MXh. rewrite DN. subst mx. unfold round_up. clear.
        pose proof (Z.le_max_r size 8). Z.div_mod_to_equations. lia. }
    match goal with |- context [Z_to_bv 64 (Z.land ?x 8)] => replace (Z_to_bv 64 (Z.land x 8)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K.
    { exfalso. apply K. rewrite ?unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - NK; try acb. lia. }
    clear K.
    (* [comment removed for export] *)
    step. step. replace (v_sltiu (Z_to_bv 64 size) 1) with (Z_to_bv 64 0).
    2:{ rewrite v_sltiu_b2z. rewrite (unsigned_lit size) by lia. change (bv_wrap 64 1) with 1. rewrite zb_b2z_if. destruct (Z.ltb_spec size 1); [lia| reflexivity]. }
    (* [comment removed for export] *)
    step. step. match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => replace (Z_to_bv 64 (bv_swrap 32 x)) with (Z_to_bv 64 2048) by (apply bv_eq; vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    step. step. step. replace (v_sltu (Z_to_bv 64 8) (Z_to_bv 64 65537)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    step. replace (needed - 4096 + 2048) with (needed - 2048) by lia.
    (* [comment removed for export] *)
    step. replace (v_sltu (Z_to_bv 64 (needed - 2048)) (Z_to_bv 64 65537)) with (Z_to_bv 64 0).
    2:{ rewrite v_sltu_b2z. rewrite (unsigned_lit (needed - 2048)), (unsigned_lit 65537) by lia. rewrite zb_b2z_if. destruct (Z.ltb_spec (needed - 2048) 65537); [lia| reflexivity]. }
    step. step. step. step. step.
    replace (2048 + (needed - 2048)) with needed by lia.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. callD getcurthread_spec. all: rewrite ?unsigned_lit by lia. all: try (first [exact MI | exact ST | exact LO | exact Etsdi | exact Etp | exact Etsd | exact Ectx | eassumption]); try (first [clear - HI BND; lia | lia]).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; lia). all: try (unfold AIMG_TOP; lia).
    unfold wz.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. step.
    apply evt_done. unfold PREPOST, alloc_pre_sec_post, wz, AINST. do 12 eexists. exists j8.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact (aenv_now_pre_sec _ _ ENV0 MUB WMB)|]. split; [exact FR| eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partB_pre_sec : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch Wpre m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    evt asegs PREPOST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 8) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz 8) (wz 7) x20 (wz size) (wz AINST) (wz SO) x24 (wz 7) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196f68) fc None mB (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI MU WM FR ST.
    pose proof (munch_refl Wpre mB) as MUB. pose proof (wmono_refl asegs mB) as WMB. unfold Wpre in MUB.
    unfold Wpre in MU. prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST. region_table.
    (* [comment removed for export] *)
    step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => replace (Z_to_bv 64 (Z.land x y)) with (wz 16) by (apply bv_eq; vm_compute; reflexivity) end.
    step. callD rzlog16_spec. all: try reflexivity. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => replace (Z_to_bv 64 (Z.land x y)) with (wz 2048) by (apply bv_eq; vm_compute; reflexivity) end.
    step. callD rzlog2048_spec. all: try reflexivity. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.
    unfold wz.
    (* [comment removed for export] *)
    step. if_cases K1. 2:{ exfalso. revert K1. vm_compute. discriminate. } clear K1.
    step. if_cases K2. { exfalso. revert K2. vm_compute. discriminate. } clear K2.
    step. step. step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. } clear K3.
    step.
    replace (Z_to_bv 64 size) with (Z_to_bv 64 (Z.max size 8)) at 2 by (f_equal; lia).
    eapply partC_pre_sec; try eassumption. exact (aenv_now_pre_sec _ _ ENV0 MUB WMB).
  Qed.

  (* [comment removed for export] *)
  Hypotheses (Ha0 : a0 = wz AINST) (Ha1 : a1 = wz size) (Ha2 : a2 = wz 8) (Ha3 : a3 = wz SO) (Ha4 : a4 = wz 1) (Ha5 : a5 = wz 1).
  Theorem allocate_pre_sec :
    AENV tp TSD CTX TH sb SO T rest m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    evt asegs PREPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x196dfc) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
    pose proof (munch_refl Wpre m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold Wpre in MU. prep. unfold wz in *. unfold AINST. region_table.
    (* [comment removed for export] *)
    step. carve_frame 128%nat ST.
    do 13 step. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV' : AENV tp TSD CTX TH sb SO T rest mm) by (eapply aenv_now_pre_sec; [exact ENV| exact MU| exact WM]) end.
    pose proof ENV as ENV0. clear ENV. open_env ENV'. unfold wz in *.
    (* [comment removed for export] *)
    step. callD asan_inited_spec. all: try (unfold AINITED; eassumption).
    step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. callD rss_exceeded_spec. all: try (unfold AALLOCFLAGS; eassumption).
    step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    do 13 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 112)] => replace (Z_to_bv 64 (Z.land x 112)) with (Z_to_bv 64 16) by (apply bv_eq; vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    step. step. step. step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. step. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. 2:{ exfalso. lia. } clear K0.
    step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. 2:{ exfalso. lia. } clear K1.
    step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. 2:{ exfalso. lia. } clear K2.
    step. step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. } clear K3.
    step. step. step. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. } clear K4.
    step. step. step. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia. 2:{ exfalso. lia. } clear K5.
    step. step. step. step.
    rewrite v_sltu_b2z. rewrite (unsigned_lit size), (unsigned_lit 64513) by lia. rewrite zb_b2z_if.
    destruct (Z.ltb_spec size 64513); [exfalso; lia|].
    change (Z.lxor (bv_unsigned (Z_to_bv 64 0)) 7) with 7.
    eapply partB_pre_sec; try eassumption. econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr].
  Qed.
End AllocPreSec.

