From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform ObjUnbase TobjJV TobjArena TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Str_memcpy__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require S_fsB.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require Import fsB_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import fsT_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma In_of_in : forall (f : sprop) (l : list sprop), fs_st.in_facts f l = true -> In f l.
Proof.
  intros f l. induction l as [|g t IH]; cbn; intros H; [discriminate|].
  apply orb_true_iff in H as [H|H]; [left; symmetry; exact (sprop_eqb_sound _ _ H) | right; exact (IH H)].
Qed.
Ltac getb HF p H :=
  lazymatch type of HF with
  | Forall _ ?l =>
      let E := fresh "E" in
      assert (E : fs_st.in_facts p l = true) by (vm_compute; reflexivity);
      pose proof (proj1 (Forall_forall _ l) HF p (In_of_in p l E)) as H; clear E
  end.

Lemma ule_lit : forall rho x c, holds rho (SPUle x (SLit c)) -> 0 <= c < M64v -> bv_unsigned (eval rho x) <= c.
Proof. intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.
Ltac ule H := exact (ule_lit _ _ _ H ltac:(unfold M64v, two47, S_vr.hiA; lia)).
Ltac ule47 H := eapply Z.le_trans; [exact (ule_lit _ _ _ H ltac:(unfold M64v, two47, S_vr.hiA; lia)) | unfold two47, S_vr.hiA; lia].
Lemma ub47_of : forall rho c B, holds rho (SPUle (SVar c) (SLit B)) -> 0 <= B <= two47 -> bv_unsigned (rw rho c) <= two47.
Proof. intros rho c B H HB. rewrite <- eval_var. pose proof (ule_lit _ _ _ H ltac:(unfold M64v, two47 in *; lia)). lia. Qed.
Lemma ule_var : forall rho c k B, holds rho (SPUle (SVar c) (SVar k)) -> bv_unsigned (rw rho k) <= B -> bv_unsigned (rw rho c) <= B.
Proof. intros rho c k B H HB. cbn [holds] in H. rewrite !eval_var in H. lia. Qed.
Ltac b47 := unfold two47, S_vr.hiA; lia.

Definition o128 (c : positive) : sv := SMd M_MUL (SLit 128) (SVar c).

(* the slot [128c, 128c+128) lies inside the data block [0, 128K) *)
Lemma sf_ok : forall rho c K,
  holds rho (SPUle (SAlu ALU_ADD (SVar c) (SLit 1)) (SVar K)) ->
  bv_unsigned (rw rho c) <= two47 -> bv_unsigned (rw rho K) <= two47 ->
  Forall (holds rho) [SPUle (o128 c) (o128 K); SPUle (SAlu ALU_ADD (o128 c) (SLit 128)) (o128 K)].
Proof.
  intros rho c K H Hc HK. unfold o128. cbn [holds] in H. rewrite U_add, U_lit, !eval_var in H.
  unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho c)) as Rc. pose proof (bv_urange (rw rho K)) as RK.
  rewrite (Z.mod_small 1) in H by lia. rewrite (Z.mod_small (_ + 1)) in H by lia.
  apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
  all: cbn [holds]; rewrite ?U_add, ?U_mul, ?U_lit, ?eval_var; unfold M64v;
    rewrite ?(Z.mod_small 128) by lia; rewrite ?(Z.mod_small (128 * bv_unsigned (rw rho c))) by nia;
    rewrite ?(Z.mod_small (128 * bv_unsigned (rw rho K))) by nia;
    rewrite ?(Z.mod_small (128 * bv_unsigned (rw rho c) + 128)) by nia; nia.
Qed.

(* the slot object [d+128c, +128) and the middle piece [128c, 128c+128) of the data object based at d cover the
   same bytes *)
Lemma slot_rng : forall rho d c,
  bv_unsigned (rw rho d) <= two47 -> bv_unsigned (rw rho c) <= two47 ->
  bv_unsigned (eval rho (SAlu ALU_ADD (SVar d) (o128 c))) + soff rho (SLit 0) =
    bv_unsigned (eval rho (SVar d)) + soff rho (o128 c) /\
  bv_unsigned (eval rho (SAlu ALU_ADD (SVar d) (o128 c))) + soff rho (SLit 128) =
    bv_unsigned (eval rho (SVar d)) + soff rho (SAlu ALU_ADD (o128 c) (SLit 128)).
Proof.
  intros rho d c Hd Hc. unfold o128, two47 in *.
  rewrite !soff_lit_small by lia. unfold soff. rewrite !bv_signed_U. rewrite !U_add, !U_mul, !U_lit, !eval_var.
  unfold M64v. pose proof (bv_urange (rw rho c)) as Rc. pose proof (bv_urange (rw rho d)) as Rd.
  rewrite (Z.mod_small 128) by lia. rewrite (Z.mod_small (128 * _)) by nia.
  rewrite (Z.mod_small (_ + 128 * _)) by nia. rewrite (Z.mod_small (128 * _ + 128)) by nia.
  destruct (Zsigned_spec (128 * bv_unsigned (rw rho c))) as [[_ X1]|[X1 _]]; [|lia].
  destruct (Zsigned_spec (128 * bv_unsigned (rw rho c) + 128)) as [[_ X2]|[X2 _]]; [|lia].
  rewrite X1, X2. lia.
Qed.

Lemma perm_mid : forall {A} (l1 l2 : list A) x, Permutation (l1 ++ x :: l2) ((l1 ++ l2) ++ [x]).
Proof. intros. apply TobjJVx.perm_move_last. Qed.

Lemma tv0_kp : Permutation tv0 (tv_k ++ tv_p).
Proof.
  replace tv0 with (firstn 7 tv0 ++ nth 7 tv0 (SLit 0, SLit 0) :: skipn 8 tv0) by (vm_compute; reflexivity).
  replace (tv_k ++ tv_p) with ((firstn 7 tv0 ++ skipn 8 tv0) ++ [nth 7 tv0 (SLit 0, SLit 0)]) by (vm_compute; reflexivity).
  apply perm_mid.
Qed.
Lemma tvG_kp : Permutation (tv_k ++ tv_gp) tvG.
Proof.
  replace tvG with (firstn 7 tv0 ++ nth 0 tv_gp (SLit 0, SLit 0) :: skipn 8 tv0) by (vm_compute; reflexivity).
  replace (tv_k ++ tv_gp) with ((firstn 7 tv0 ++ skipn 8 tv0) ++ [nth 0 tv_gp (SLit 0, SLit 0)]) by (vm_compute; reflexivity).
  apply Permutation_sym, perm_mid.
Qed.

Definition to_fs_ok (X : sstate) (p : list nat) : bool :=
  match unbase_obj_at X 0 16 with
  | Some X1 => match apply_xforms X1 [XSelect sel_fp; XMerge 0; XSplit 0 (SLit (-48))] with
    | Some X2 => match unbase_obj_at X2 0 (-48) with
      | Some X3 => match apply_xforms X3 [XSelect p] with
        | Some Y => match apply_xforms Y (xs_reb Y) with Some _ => true | None => false end
        | None => false end
      | None => false end
    | None => false end
  | None => false end.

Lemma SPJ_to_fs : forall J rho X p w, to_fs_ok X p = true -> SPJ segsU J X rho w -> SPJ segsU J (to_fs X p) rho w.
Proof.
  intros J rho X p w Hok H. unfold to_fs_ok in Hok. unfold to_fs, sel_X, fs_lay0, ub, optS.
  destruct (unbase_obj_at X 0 16) as [X1|] eqn:E1; [|discriminate].
  destruct (apply_xforms X1 [XSelect sel_fp; XMerge 0; XSplit 0 (SLit (-48))]) as [X2|] eqn:E2; [|discriminate].
  destruct (unbase_obj_at X2 0 (-48)) as [X3|] eqn:E3; [|discriminate].
  destruct (apply_xforms X3 [XSelect p]) as [Y|] eqn:E4; [|discriminate].
  destruct (apply_xforms Y (xs_reb Y)) as [Z|] eqn:E5; [|discriminate].
  apply (SPJ_xforms segsU J _ rho Y Z w E5), (SPJ_xforms segsU J _ rho X3 Y w E4), (SPJ_unbase segsU J rho X2 0 (-48) X3 w E3),
    (SPJ_xforms segsU J _ rho X1 X2 w E2), (SPJ_unbase segsU J rho X 0 16 X1 w E1). exact H.
Qed.

Lemma Posts_mc_eq : MC.Posts_memcpy = [L_mcA; L_mcB].
Proof. vm_compute. reflexivity. Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv am.
Let Q : assn := LQP segsU FD.NP rho0 (Posts_fs Kc FB).

Lemma ejcert_ok : ejcertA segsU FD.NP FUEL_T cutpcs_T 200 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma JGv_perm : forall tv tv' am S rho w, Permutation tv tv' -> SPJ segsU (JGv tv am) S rho w -> SPJ segsU (JGv tv' am) S rho w.
Proof. intros. exact (TobjJVAx.SPJ_JGA_perm segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv tv' am S rho w H H0). Qed.

(* the data block of the sh vector is live once the vector holds an element *)
Lemma sh_tv_facts : forall rho tr md, JGv tv0 amT rho tr md -> Forall (holds rho) (ss_facts T_vpk) ->
  Forall (holds rho) (tv_facts tv_sh).
Proof.
  intros rho tr md HJ HF.
  getb HF (SPUle (SAlu ALU_ADD (SVar 111) (SLit 1)) (SVar 112)) Hc.
  getb HF (SPUle (SVar 112) (SLit two47)) HK. getb HF (SPUle (SVar 111) (SVar 112)) Hck.
  assert (Hin : In tv_sh tv0) by (vm_compute; tauto).
  apply (JGA_tv_facts segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv0 amT rho tr md tv_sh HJ Hin).
  intros Hz0. pose proof HJ as (Ai & (_ & _ & _ & _ & (_ & _ & HZ) & _) & _).
  pose proof (proj1 (Forall_forall _ _) HZ _ Hin (fun X => X Hz0)) as Z0.
  unfold tvv, tv_sh, d_sh, k_sh in Z0. cbn [snd] in Z0. rewrite U_mul, U_lit, eval_var in Z0.
  apply ule_lit in HK; [|unfold M64v, two47; lia]. rewrite eval_var in HK.
  cbn [holds] in Hc, Hck. rewrite U_add, U_lit, !eval_var in Hc. rewrite !eval_var in Hck.
  unfold M64v, two47 in *. pose proof (bv_urange (rw rho 111%positive)) as R1. pose proof (bv_urange (rw rho 112%positive)) as R2.
  rewrite (Z.mod_small 1) in Hc by lia. rewrite (Z.mod_small (_ + 1)) in Hc by lia.
  rewrite (Z.mod_small 128) in Z0 by lia. rewrite Z.mod_small in Z0 by nia. lia.
Qed.

(* carve the memcpy operands out of their objects, and merge them back after the call *)
Ltac carve_tac E0 E2 E3 E K d fK fd :=
  let rho := fresh "rho" in let w := fresh "w" in let Hw := fresh "Hw" in
  intros rho w Hw;
  let i := eval vm_compute in (i_dat E0 + 3)%nat in
  let o := eval vm_compute in (nth i (ss_objs E3) O_AF) in
  let o' := eval vm_compute in (slot_obj E0) in
  replace E with (reshape_obj_at E3 i o') by (vm_compute; reflexivity);
  apply (SPJ_reshape segsU _ rho E3 i o o' w);
  [ vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | let HF := fresh "HF" in let Hd1 := fresh "Hd1" in let Hc1 := fresh "Hc1" in let Hk0 := fresh "Hk0" in intros HF;
    getb HF fd Hd1; getb HF (SPUle (SVar 111) (SVar 112)) Hc1; getb HF (SPUle (SVar 112) (SLit two47)) Hk0;
    unfold obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi];
    exact (slot_rng rho d 111 (ub47_of _ _ _ Hd1 ltac:(b47)) (ule_var _ _ _ _ Hc1 (ub47_of _ _ _ Hk0 ltac:(b47))))
  | eapply (SPJ_unbase segsU _ rho E2 1 (-184) E3 w); [vm_compute; reflexivity|];
    eapply (SPJ_xforms segsU _ (xs_mc E0) rho (add_facts (sfacts E0) E0) E2 w); [vm_compute; reflexivity|];
    apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |];
    let tr := fresh "tr" in let md := fresh "md" in let HF := fresh "HF" in
    let Hc2 := fresh "Hc2" in let Hc3 := fresh "Hc3" in let Hk0 := fresh "Hk0" in let HkK := fresh "HkK" in
    intros tr md _ HF;
    replace (sfacts E0) with [SPUle (o128 111) (o128 K); SPUle (SAlu ALU_ADD (o128 111) (SLit 128)) (o128 K)]
      by (vm_compute; reflexivity);
    getb HF (SPUle (SAlu ALU_ADD (SVar 111) (SLit 1)) (SVar K)) Hc2; getb HF (SPUle (SVar 111) (SVar 112)) Hc3;
    getb HF (SPUle (SVar 112) (SLit two47)) Hk0; getb HF fK HkK;
    exact (sf_ok rho 111 K Hc2 (ule_var _ _ _ _ Hc3 (ub47_of _ _ _ Hk0 ltac:(b47))) (ub47_of _ _ _ HkK ltac:(b47))) ].

Lemma carve_k : forall rho w, SPJ segsU (JGv tv0 amT) E_mk0 rho w -> SPJ segsU (JGv tv0 amT) E_mk rho w.
Proof. carve_tac E_mk0 E_mk2 E_mk3 E_mk 112%positive 110%positive (SPUle (SVar 112) (SLit two47)) (SPUle (SVar 110) (SLit two47)). Qed.
Lemma carve_g : forall rho w, SPJ segsU (JGv tvG amT) E_mg0 rho w -> SPJ segsU (JGv tvG amT) E_mg rho w.
Proof. carve_tac E_mg0 E_mg2 E_mg3 E_mg 818%positive 817%positive (SPUle (SVar 818) (SLit S_vr.hiA)) (SPUle (SVar 817) (SLit S_vr.hiA)). Qed.

Ltac unc_tac E0 E T U1 C d fd :=
  let rho := fresh "rho" in let w := fresh "w" in let Hw := fresh "Hw" in
  intros rho w Hw;
  let i := eval vm_compute in (i_dat E0 + 3)%nat in
  let o' := eval vm_compute in (mid_obj E0) in
  let o := eval vm_compute in (nth i (ss_objs U1) O_AF) in
  eapply (SPJ_xforms segsU _ (xs_unc E0) rho (reshape_obj_at U1 i o') C w); [vm_compute; reflexivity|];
  apply (SPJ_reshape segsU _ rho U1 i o o' w);
  [ vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | let HF := fresh "HF" in let Hd1 := fresh "Hd1" in let Hc1 := fresh "Hc1" in let Hk0 := fresh "Hk0" in intros HF;
    getb HF fd Hd1; getb HF (SPUle (SVar 111) (SVar 112)) Hc1; getb HF (SPUle (SVar 112) (SLit two47)) Hk0;
    unfold obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi];
    let A := fresh "A" in let B := fresh "B" in
    destruct (slot_rng rho d 111 (ub47_of _ _ _ Hd1 ltac:(b47)) (ule_var _ _ _ _ Hc1 (ub47_of _ _ _ Hk0 ltac:(b47)))) as [A B];
    split; [symmetry; exact A | symmetry; exact B]
  | exact (SPJ_xforms segsU _ [XSelect (cperm E T)] rho T U1 w ltac:(vm_compute; reflexivity) Hw) ].

Lemma unc_kA : forall rho w, SPJ segsU (JGv tv0 amT) T_mkA rho w -> SPJ segsU (JGv tv0 amT) C_mkA rho w.
Proof. unc_tac E_mk0 E_mk T_mkA U_mkA1 C_mkA 110%positive (SPUle (SVar 110) (SLit two47)). Qed.
Lemma unc_kB : forall rho w, SPJ segsU (JGv tv0 amT) T_mkB rho w -> SPJ segsU (JGv tv0 amT) C_mkB rho w.
Proof. unc_tac E_mk0 E_mk T_mkB U_mkB1 C_mkB 110%positive (SPUle (SVar 110) (SLit two47)). Qed.
Lemma unc_gA : forall rho w, SPJ segsU (JGv tvG amT) T_mgA rho w -> SPJ segsU (JGv tvG amT) C_mgA rho w.
Proof. unc_tac E_mg0 E_mg T_mgA U_mgA1 C_mgA 817%positive (SPUle (SVar 817) (SLit S_vr.hiA)). Qed.
Lemma unc_gB : forall rho w, SPJ segsU (JGv tvG amT) T_mgB rho w -> SPJ segsU (JGv tvG amT) C_mgB rho w.
Proof. unc_tac E_mg0 E_mg T_mgB U_mgB1 C_mgB 817%positive (SPUle (SVar 817) (SLit S_vr.hiA)). Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall (J : jpred) (S : sstate) (rho : valuation) (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_callP : forall (J Jp : jpred) (C Pre : sstate) (s : wsub) (R : list sobj)
  (Posts : list (sstate * jpost)) (Q' : assn) (rho : valuation),
  entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQP segsU (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md', In (L, JL) Posts ->
     smatch segsU rho C (tr, mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segsU rhoL L (tr', mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis TR_callJ : ltac:(let t := type of (pure_callAT segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML TR TR_facts TR_pre) in
  lazymatch t with forall _ : ?A, _ => exact A end).
Hypothesis CVP : forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc S_vr.P0_vr FBc S_vr.tv0 (AHead (SVar hVP))) S_vp.Pre_vp rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc (fun _ => S_vr.P0_vr) (PDAh S_vp.PD_vp hVP) FBc)).
Hypothesis CMC : forall (tv : list (sv * sv)) (am : amode) (rho rho1 : valuation),
  TR (SP segsU (fun tr md => JGv tv am rho tr md) MC.Pre_memcpy rho1)
     (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next MC.Pre_memcpy) rho1 MC.Posts_memcpy).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_fs FB) FB tv am) (Posts_fs Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let CALLVP := client_callAT segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML (fun _ => S_vr.P0_vr) S_vp.Pre_vp S_vr.tv0
  (AHead (SVar hVP)) (PDAh S_vp.PD_vp hVP) NF (@eq_refl positive (ss_next S_vp.Pre_vp)) TR TR_facts TR_ex TR_pre TR_callP CVP.
Let PURE := pure_callAT segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML TR TR_facts TR_pre TR_callJ.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof. intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac inlist := repeat first [left; reflexivity | right].
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT);
  [unfold cutsE; inlist | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].
Ltac vmr := vm_compute; reflexivity.

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0 amq) P_fail rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_failz : forall rho b, TR (SPJ segsU (JGv tv0 amq) P_failz rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tvOK amq) P_ok rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.

(* vp (vec_push of the shape vector) *)
Lemma P0_vr_ok : forall rho R ms, Forall (holds rho) (ss_facts E_vp) -> tvz rho (tv_k ++ tv_p) ->
  S_vr.P0_vr (rho_sub (rho_absorb rho R ms) s_vp).
Proof.
  intros rho R ms HF HZ. unfold S_vr.P0_vr. rewrite !rw_call'.
  change (wsub_get s_vp 17%positive) with (SVar 112). change (wsub_get s_vp 15%positive) with (SVar 110).
  rewrite !eval_var. intros Hk Hd. apply Hk.
  assert (Hin : In tv_sh (tv_k ++ tv_p)) by (vm_compute; tauto).
  pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Ht. unfold tnz, tvv, tv_sh, d_sh, k_sh in Ht. cbn [fst snd] in Ht.
  rewrite eval_var in Ht. specialize (Ht ltac:(intros Y; exact (Y Hd))).
  getb HF (SPUle (SVar 112) (SLit two47)) HK. apply ule_lit in HK; [|unfold M64v, two47; lia]. rewrite eval_var in HK.
  rewrite U_mul, U_lit, eval_var in Ht. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho 112%positive)) as Rk.
  rewrite (Z.mod_small 128) in Ht by lia. rewrite Z.mod_small in Ht by nia. lia.
Qed.

Lemma X_E_vp : forall rho, TR (SPJ segsU (JGv tv0 amT) E_vp0 rho) (FAM (ameas ((E_vp0, (tv0, amT)), (95, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (CALLVP E_vp s_vp R_vp rho tv_k tv_p amT); [vmr | vmr | vmr | vmr | vmr | vmr | vmr | vmr | vmr | |].
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split.
    + apply (robjs_checkF_sound segsU C_U rho0 FB rho (ss_facts E_vp) tv_k (fun _ => false) R_vp HF
               (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT));
        [ exact (TobjJVAy.tvz_app_l rho tv_k tv_p HZ) | vmr | intros o a Ho Hx; discriminate Hx ].
    + exact (P0_vr_ok rho R_vp ms HF HZ).
  - intros d rho' Hd Hag. unfold PDAh, S_vp.PD_vp in Hd. cbn [map] in Hd.
    destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    + change (T_afterN NF E_vp s_vp R_vp S_vp.P_push_fail) with T_vpf.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with (tv_k ++ tv_p) by vmr; replace am with amT by vmr end.
      eapply TR_pre; [ | reenter C_vpf tv0 amT 90 z0 ].
      intros w Hw. apply (JGv_perm _ _ _ _ _ _ (Permutation_sym tv0_kp)).
      replace C_vpf with (to_fs T_vpf p_f) by vmr.
      exact (SPJ_to_fs _ _ T_vpf p_f w ltac:(vmr) Hw).
    + change (T_afterN NF E_vp s_vp R_vp S_vp.P_push_keep) with T_vpk.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with (tv_k ++ tv_p) by vmr; replace am with amT by vmr end.
      eapply TR_pre; [ | reenter C_vpk tv0 amT 90 z0 ].
      intros w Hw. apply (JGv_perm _ _ _ _ _ _ (Permutation_sym tv0_kp)) in Hw.
      replace C_vpk with (to_fs (add_facts (tv_facts tv_sh) T_vpk) p_k) by vmr.
      apply (SPJ_to_fs _ _ (add_facts (tv_facts tv_sh) T_vpk) p_k w ltac:(vmr)).
      apply SPJ_refacts_J; [exact Hw | vmr |]. intros tr md HJ HF. exact (sh_tv_facts rho' tr md HJ HF).
    + change (T_afterN NF E_vp s_vp R_vp S_vp.P_push_grown) with T_vpg.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with (tv_k ++ tv_gp) by vmr; replace am with amT by vmr end.
      eapply TR_pre; [ | reenter C_vpg tvG amT 90 z0 ].
      intros w Hw. apply (JGv_perm _ _ _ _ _ _ tvG_kp).
      replace C_vpg with (to_fs T_vpg p_k) by vmr.
      exact (SPJ_to_fs _ _ T_vpg p_k w ltac:(vmr) Hw). }
  intros w Hw. apply (JGv_perm _ _ _ _ _ _ tv0_kp) in Hw.
  eapply (SPJ_unbase segsU _ rho E_vp2 1 (-208) E_vp w); [vmr|].
  eapply (SPJ_unbase segsU _ rho E_vp1 2 (-192) E_vp2 w); [vmr|].
  exact (SPJ_xforms segsU _ xs_vp rho E_vp0 E_vp1 w ltac:(vmr) Hw).
Qed.

Lemma X_E_mk : forall rho, TR (SPJ segsU (JGv tv0 amT) E_mk0 rho) (FAM (ameas ((E_mk0, (tv0, amT)), (85, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (PURE E_mk MC.Pre_memcpy s_mk R_mk MC.Posts_memcpy rho tv0 amT _ (CMC tv0 amT rho)); [vmr | vmr | vmr | vmr | vmr | vmr |].
       intros L rho' HL _. rewrite Posts_mc_eq in HL. destruct HL as [<-|[<-|[]]].
       - replace (add_facts (ss_facts E_mk) (import_post s_mk (ss_next MC.Pre_memcpy) (lf_state L_mcA) (ss_next E_mk) R_mk))
           with T_mkA by vmr.
         eapply TR_pre; [ | reenter C_mkA tv0 amT 80 z0 ]. intros w Hw. exact (unc_kA rho' w Hw).
       - replace (add_facts (ss_facts E_mk) (import_post s_mk (ss_next MC.Pre_memcpy) (lf_state L_mcB) (ss_next E_mk) R_mk))
           with T_mkB by vmr.
         eapply TR_pre; [ | reenter C_mkB tv0 amT 80 z0 ]. intros w Hw. exact (unc_kB rho' w Hw). }
  intros w Hw. exact (carve_k rho w Hw).
Qed.

Lemma X_E_mg : forall rho, TR (SPJ segsU (JGv tvG amT) E_mg0 rho) (FAM (ameas ((E_mg0, (tvG, amT)), (85, z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (PURE E_mg MC.Pre_memcpy s_mg R_mg MC.Posts_memcpy rho tvG amT _ (CMC tvG amT rho)); [vmr | vmr | vmr | vmr | vmr | vmr |].
       intros L rho' HL _. rewrite Posts_mc_eq in HL. destruct HL as [<-|[<-|[]]].
       - replace (add_facts (ss_facts E_mg) (import_post s_mg (ss_next MC.Pre_memcpy) (lf_state L_mcA) (ss_next E_mg) R_mg))
           with T_mgA by vmr.
         eapply TR_pre; [ | reenter C_mgA tvG amT 80 z0 ]. intros w Hw. exact (unc_gA rho' w Hw).
       - replace (add_facts (ss_facts E_mg) (import_post s_mg (ss_next MC.Pre_memcpy) (lf_state L_mcB) (ss_next E_mg) R_mg))
           with T_mgB by vmr.
         eapply TR_pre; [ | reenter C_mgB tvG amT 80 z0 ]. intros w Hw. exact (unc_gB rho' w Hw). }
  intros w Hw. exact (carve_g rho w Hw).
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <- <-.
  - apply X_E_vp.
  - apply X_E_mk.
  - apply X_E_mg.
  - apply X_P_fail.
  - apply X_P_failz.
  - apply X_P_ok.
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis VPS : S_vp.vp_stmt_U.

Theorem fsT_sum : forall rho, triple segsU ok (SPJ segsU (JGv tv0 amT) J1236 rho) Q.
Proof.
  intros rho.
  apply (cfg_sound_JGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL_T cutpcs_T 200 cutsE exitsE ok Q (proj1 HS)
           (ejcertA_jcertA segsU FD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
  apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
           (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
           (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_soundP segsU ok) (call_soundJ segsU ok)).
  - intros FBc rho1.
    exact (JGA_frame_sum segsU C_U Kc (fun _ => S_vr.P0_vr) S_vp.Pre_vp S_vr.tv0 S_vp.PD_vp NF hVP ML eq_refl
             (fun F F' r _ H => H) ok (fun FBc' rho2 => VPS ok Kc FBc' rho2 HS ML MC) FBc rho1).
  - intros tv am rho' rho1. apply MC.memcpy_sum.
    exact (ok_frameJ_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ok tv am (proj1 HS) rho').
  - intros T tv am rT vT rho' b Hin _ _. exact (reenter_cutGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ok cutsE T tv am (rT, vT) Q rho' Hin).
  - intros P tv am rho' b Hin. apply (exit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB ok rho0 tv am (Posts_fs Kc FB) P). exact Hin.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis VPX : S_vp.vp_ex_stmt_U.

Theorem fsT_sum_ex : forall rho, etriple segsU (SPJ segsU (JGv tv0 amT) J1236 rho) Q.
Proof.
  intros rho.
  apply (cfg_complete_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL_T cutpcs_T 200 cutsE exitsE Q ejcert_ok)
    with (rvT := (100, z0)); [|left; reflexivity].
  apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB) cutsE) b w \/ Q w)
           (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
           (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_completeP segsU) (call_completeJ segsU)).
  - intros FBc rho1.
    exact (JGA_frame_sum_ex segsU C_U Kc (fun _ => S_vr.P0_vr) S_vp.Pre_vp S_vr.tv0 S_vp.PD_vp NF hVP ML eq_refl
             (fun F F' r _ H => H) (fun FBc' rho2 => VPX Kc FBc' rho2 Hvi ML MCX) FBc rho1).
  - intros tv am rho' rho1. apply MC.memcpy_sum_ex.
  - intros T tv am rT vT rho' b Hin H0 Hb. apply (ereenter_cutAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB cutsE T tv am (rT, vT) Q b rho' Hin).
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho' vT)). nia.
  - intros P tv am rho' b Hin. apply (eexit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB rho0 tv am (Posts_fs Kc FB) P). exact Hin.
Qed.
End Existence.
End Sum.

Theorem fsT_sum_U : S_vp.vp_stmt_U -> S_fsB.fsB_stmt J1236 h1236.
Proof. intros VPS ok Kc FB rho0 rho HS ML MC. exact (fsT_sum ok Kc FB rho0 HS ML MC VPS rho). Qed.

Theorem fsT_ex_U : S_vp.vp_ex_stmt_U -> S_fsB.fsB_ex_stmt J1236 h1236.
Proof. intros VPX Kc FB rho0 rho Hvi ML MCX. exact (fsT_sum_ex Kc FB rho0 ML Hvi MCX VPX rho). Qed.
