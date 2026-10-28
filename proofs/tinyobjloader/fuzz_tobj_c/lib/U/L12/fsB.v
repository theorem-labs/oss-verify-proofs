From Stdlib Require Import ZArith NArith List Bool PArith Lia.
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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_vf S_ad.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require fs_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require Import S_fsB fsB_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition z0 : sv := SLit 0.
Definition FUEL : nat := 3000%nat.
Definition amh (h : positive) : amode := AHead (SVar h).
Definition amx (X : sstate) : amode := AHead (headv X).

Definition cutsE : list aedesc :=
  [ (J, (tv0, amh fs_st.hJ852), (100, z0));
    (C1z, (tv0, amx C1z), (90, z0)); (C1f, (tv0, amx C1f), (90, z0)); (C1o, (tv0, amx C1o), (90, z0));
    (J892, (tv0, amh h892), (85, z0));
    (C2z, (tv0, amx C2z), (75, z0)); (C2f, (tv0, amx C2f), (75, z0)); (C2o, (tv0, amx C2o), (75, z0));
    (J932, (tv0, amh h932), (70, z0));
    (C3z, (tv0, amx C3z), (60, z0)); (C3f, (tv0, amx C3f), (60, z0)); (C3o, (tv0, amx C3o), (60, z0));
    (J1344a, (tv0, amh h1344a), (20, z0)); (J1344b, (tv0, amh h1344b), (20, z0)); (J1344c, (tv0, amh h1344c), (20, z0)) ].
Definition exitsE : list aedesc :=
  [ (E1, (tv0, amh fs_st.hJ852), (95, z0));
    (E2, (tv0, amh h892), (80, z0));
    (E3, (tv0, amh h932), (65, z0));
    (J1236, (tv0, amh h1236), (30, z0));
    (XFa1, (tv0, amh h1344a), (10, z0)); (XFa2, (tv0, amh h1344a), (10, z0));
    (XFb1, (tv0, amh h1344b), (10, z0)); (XFb2, (tv0, amh h1344b), (10, z0));
    (XFc1, (tv0, amh h1344c), (10, z0)); (XFc2, (tv0, amh h1344c), (10, z0)) ].

Lemma ejcert_ok : ejcertA segsU FD.NP FUEL cps 200 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition tvK : list (sv * sv) := Eval vm_compute in firstn 8 tv0.

Lemma back_ok : forall J0 X rb Y rho w, back_o X rb = Some Y -> SPJ segsU J0 X rho w -> SPJ segsU J0 Y rho w.
Proof.
  intros J0 X rb Y rho w H Hw. unfold back_o in H.
  destruct (apply_xforms X (xs_back rb)) as [X1|] eqn:E1; [|discriminate].
  destruct (unbase_obj_at X1 1 (-192)) as [X2|] eqn:E2; [|discriminate].
  destruct (unbase_obj_at X2 2 (-192)) as [X3|] eqn:E3; [|discriminate].
  apply (SPJ_unbase segsU J0 rho X3 2 (-48) Y w H).
  apply (SPJ_unbase segsU J0 rho X2 2 (-192) X3 w E3).
  apply (SPJ_unbase segsU J0 rho X1 1 (-192) X2 w E2).
  exact (SPJ_xforms segsU J0 _ rho X X1 w E1 Hw).
Qed.
Lemma tv0_split : tv0 = tvK ++ [(SVar 101, SLit 64)].
Proof. reflexivity. Qed.
Definition no_extra (o : sobj) : bool := false.

(* E1 -> E1f: the vf-call frame split and the stack bound below it *)
Definition E1x : sstate := Eval vm_compute in optS (apply_xforms E1 xs_vf).
Definition E1u3 : sstate := Eval vm_compute in optS (unbase_obj_at E1x 3 (-192)).
Definition E1u2 : sstate := Eval vm_compute in optS (unbase_obj_at E1u3 2 (-224)).

Lemma fact_in : forall rho (l : list sprop) p, Forall (holds rho) l -> In p l -> holds rho p.
Proof. intros rho l p H Hin. exact (proj1 (Forall_forall _ _) H p Hin). Qed.
Ltac getf HF p H := pose proof (fact_in _ _ p HF ltac:(vm_compute; tauto)) as H.

Lemma f272_ok : forall rho, Forall (holds rho) (ss_facts E1v) -> holds rho f272.
Proof.
  intros rho HF.
  getf HF (SPUle (SVar 30) (SAlu ALU_ADD (SAlu ALU_ADD (SVar 10) (SLit (-192))) (SVar 19))) H1.
  getf HF (SPBranch BC_GE (SLit (-880)) (SVar 19)) H2.
  getf HF (SPBranch BC_GE (SVar 19) (SLit (- 2 ^ 40))) H3.
  getf HF (SPUle (SLit S_vr.loS) (SVar 10)) H4.
  getf HF (SPUle (SVar 10) (SLit two47)) H5.
  unfold f272. apply (proj2 (holds_ule _ _ _)).
  apply (proj1 (holds_ule _ _ _)) in H1. apply (proj1 (holds_ule _ _ _)) in H4. apply (proj1 (holds_ule _ _ _)) in H5.
  apply (proj1 (holds_bge _ _ _)) in H2. apply (proj1 (holds_bge _ _ _)) in H3.
  rewrite !U_add, !U_lit, !eval_var in *.
  change (Zsigned ((-880) mod M64v)) with (-880) in H2.
  change (Zsigned ((- 2 ^ 40) mod M64v)) with (-1099511627776) in H3.
  unfold M64v, S_vr.loS, two47 in *.
  pose proof (bv_urange (rw rho 10%positive)) as R10. pose proof (bv_urange (rw rho 19%positive)) as R19.
  pose proof (bv_urange (rw rho 30%positive)) as R30.
  destruct (Zsigned_spec (bv_unsigned (rw rho 19%positive))) as [[A X]|[A X]]; rewrite X in H2, H3;
    Z.div_mod_to_equations; lia.
Qed.

Lemma E1f_from : forall J0 rho w, SPJ segsU J0 E1 rho w -> SPJ segsU J0 E1f rho w.
Proof.
  intros J0 rho w Hw.
  assert (W1 : SPJ segsU J0 E1x rho w) by exact (SPJ_xforms segsU J0 xs_vf rho E1 E1x w ltac:(vm_compute; reflexivity) Hw).
  assert (W2 : SPJ segsU J0 E1u3 rho w) by exact (SPJ_unbase segsU J0 rho E1x 3 (-192) E1u3 w ltac:(vm_compute; reflexivity) W1).
  assert (W3 : SPJ segsU J0 E1u2 rho w) by exact (SPJ_unbase segsU J0 rho E1u3 2 (-224) E1u2 w ltac:(vm_compute; reflexivity) W2).
  assert (W4 : SPJ segsU J0 E1v rho w) by exact (SPJ_unbase segsU J0 rho E1u2 1 (-272) E1v w ltac:(vm_compute; reflexivity) W3).
  exact (SPJ_refacts_J segsU J0 rho E1v [f272] w W4 ltac:(vm_compute; reflexivity)
           (fun tr md _ HF => ltac:(constructor; [exact (f272_ok rho HF) | constructor]))).
Qed.

(* vf's P0 (a nonempty vector's data is a block of FBc) for a vector whose data block is tracked in kept *)
Lemma P0_vf_of_kept : forall (FB : list (Z * Z)) rho d c k e R ms s kept,
  wsub_get s 15%positive = SVar d -> wsub_get s 16%positive = SVar c -> wsub_get s 17%positive = SVar k ->
  wsub_get s 18%positive = SLit e -> 1 <= e <= 4096 ->
  In (SVar d, SMd M_MUL (SLit e) (SVar k)) kept -> tvz rho kept ->
  holds rho (SPUle (SVar c) (SVar k)) -> holds rho (SPUle (SVar k) (SLit two47)) ->
  S_vf.P0_vf (FBx FB rho kept) (rho_sub (rho_absorb rho R ms) s).
Proof.
  intros FB rho d c k e R ms s kept H15 H16 H17 H18 He Hin HZ Hck Hk.
  unfold S_vf.P0_vf, S_vf.kbytes, S_vf.vE, S_vf.vK.
  assert (Hm : eval (rho_sub (rho_absorb rho R ms) s) (SMd M_MUL (SVar 18) (SVar 17)) = eval rho (SMd M_MUL (SLit e) (SVar k)))
    by (cbn [eval]; rewrite !rw_call', H17, H18; reflexivity).
  rewrite Hm, !rw_call', H15, H16. intros Hc.
  apply (proj1 (holds_ule _ _ _)) in Hck. apply (proj1 (holds_ule _ _ _)) in Hk.
  rewrite U_lit in Hk. rewrite !eval_var in *. unfold M64v, two47 in *. rewrite (Z.mod_small (2 ^ 47)) in Hk by lia.
  pose proof (bv_urange (rw rho k)) as Rk. pose proof (bv_urange (rw rho c)) as Rc.
  assert (Hsz : bv_unsigned (eval rho (SMd M_MUL (SLit e) (SVar k))) = e * bv_unsigned (rw rho k)).
  { rewrite U_mul, U_lit, eval_var. unfold M64v. rewrite (Z.mod_small e) by lia. apply Z.mod_small. nia. }
  pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Ht. unfold tnz, tvv in Ht. cbn [fst snd] in Ht.
  rewrite Hsz, eval_var in Ht.
  assert (Hnz : bv_unsigned (rw rho d) <> 0).
  { intros Y. specialize (Ht ltac:(intros Y'; exact (Y' Y))). nia. }
  exists (bv_unsigned (eval rho (SVar d))), (bv_unsigned (eval rho (SMd M_MUL (SLit e) (SVar k)))). split.
  - apply In_FBx. right. exists (SVar d, SMd M_MUL (SLit e) (SVar k)). split; [exact Hin|]. split; [|reflexivity].
    unfold tnz. cbn [fst]. rewrite eval_var. exact Hnz.
  - rewrite eval_var. lia.
Qed.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv am.
Let Q : assn := LQP segsU FD.NP rho0 (Posts_fs Kc FB).

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall (J : jpred) (S : sstate) (rho : valuation) (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
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
Hypothesis CVF : forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_vf.P0_vf FBc) FBc S_vf.tv0 (AHead S_vf.vHD)) S_vf.Pre_vf rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_vf.P0_vf S_vf.PDA_vf FBc)).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_fs FB) FB tv am) (Posts_fs Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).
Hypothesis B1236 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1236)) J1236 rho) (FAM b).

Let CALLVF := client_callAT segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML S_vf.P0_vf S_vf.Pre_vf S_vf.tv0 (AHead S_vf.vHD)
  S_vf.PDA_vf NF (@eq_refl positive (ss_next S_vf.Pre_vf)) TR TR_facts TR_ex TR_pre TR_callP CVF.

Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT);
  [unfold cutsE; cbn [In]; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Ltac vf_cont T C p rT :=
  match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T0 _) _ =>
    replace tv with tv0 by (vm_compute; reflexivity); replace am with (amx C) by (vm_compute; reflexivity);
    replace T0 with T by (vm_compute; reflexivity) end;
  eapply TR_pre; [ | reenter C tv0 (amx C) rT z0 ];
  let w := fresh "w" in let Hw := fresh "Hw" in
  intros w Hw; exact (SPJ_xforms segsU _ [XSelect p] _ T C w ltac:(vm_compute; reflexivity) Hw).

Ltac vf_site E s R rho am d c k e Tz Tf To p Cz Cf Co rT :=
  rewrite tv0_split;
  apply (CALLVF E s R rho tvK [(SVar 101, SLit 64)] am);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | let Ai := fresh "Ai" in let ms := fresh "ms" in let HF := fresh "HF" in let HP0 := fresh "HP0" in
    let Hav := fresh "Hav" in let HP := fresh "HP" in let HN := fresh "HN" in let HD := fresh "HD" in
    let HZ := fresh "HZ" in let HXA := fresh "HXA" in let HM := fresh "HM" in let HT := fresh "HT" in
    intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT; split;
    [ eapply (robjs_checkF_sound segsU C_U rho0 FB rho (ss_facts E) tvK no_extra R HF
                (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT));
        [ exact (TobjJVAy.tvz_app_l rho _ _ HZ) | vm_compute; reflexivity | intros o a _ Hx; discriminate Hx ]
    | apply (P0_vf_of_kept FB rho d c k e R ms s tvK);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
        | vm_compute; tauto | exact (TobjJVAy.tvz_app_l rho _ _ HZ)
        | apply (fact_in _ _ _ HF); vm_compute; tauto | apply (fact_in _ _ _ HF); vm_compute; tauto ] ]
  | let dd := fresh "dd" in let rho' := fresh "rho'" in let Hd := fresh "Hd" in let Hag := fresh "Hag" in
    intros dd rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd];
    [ vf_cont Tz Cz p rT | vf_cont Tf Cf p rT | vf_cont To Co p rT ] ].

Lemma X_E1 : forall rho,
  TR (SPJ segsU (JGv tv0 (amh fs_st.hJ852)) E1 rho) (FAM (ameas ((E1, (tv0, amh fs_st.hJ852)), (95, z0)) rho)).
Proof using CVF ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho. eapply TR_pre; [ intros w Hw; exact (E1f_from _ rho w Hw) | ].
  vf_site E1f s_v1 R_v1 rho (amh fs_st.hJ852) 125%positive 126%positive 127%positive 12 T1z T1f T1o p1 C1z C1f C1o 90.
Qed.

Lemma X_E2 : forall rho,
  TR (SPJ segsU (JGv tv0 (amh h892)) E2 rho) (FAM (ameas ((E2, (tv0, amh h892)), (80, z0)) rho)).
Proof using CVF ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho.
  vf_site E2 s_v2 R_v2 rho (amh h892) 128%positive 129%positive 130%positive 4 T2z T2f T2o p2 C2z C2f C2o 75.
Qed.

Lemma X_E3 : forall rho,
  TR (SPJ segsU (JGv tv0 (amh h932)) E3 rho) (FAM (ameas ((E3, (tv0, amh h932)), (65, z0)) rho)).
Proof using CVF ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho.
  vf_site E3 s_v3 R_v3 rho (amh h932) 131%positive 132%positive 133%positive 12 T3z T3f T3o p3 C3z C3f C3o 60.
Qed.

Ltac ret_fail X rb Y P h :=
  let rho := fresh "rho" in let b := fresh "b" in let w := fresh "w" in let Hw := fresh "Hw" in
  intros rho b;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 amq) P r w));
  [ intros w Hw; exists (rho_sub rho (infer_sub FD.NP Y P));
    eapply (SPJ_entails_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML Y P (infer_sub FD.NP Y P) tv0 tv0 (amh h) amq);
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact (back_ok _ X rb Y rho w ltac:(vm_compute; reflexivity) Hw) ]
  | apply TR_exw; intros ?; apply POST; unfold Posts_fs, PostsCA, PDA_fs; cbn [map In]; tauto ].

Lemma X_Fa1 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344a)) XFa1 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFa1 [13%nat] Ya1 P_failz h1344a. Qed.
Lemma X_Fa2 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344a)) XFa2 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFa2 [13%nat] Ya2 P_fail h1344a. Qed.
Lemma X_Fb1 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344b)) XFb1 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFb1 [13%nat; 14%nat] Yb1 P_failz h1344b. Qed.
Lemma X_Fb2 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344b)) XFb2 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFb2 [13%nat; 14%nat] Yb2 P_fail h1344b. Qed.
Lemma X_Fc1 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344c)) XFc1 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFc1 [13%nat; 14%nat; 15%nat] Yc1 P_failz h1344c. Qed.
Lemma X_Fc2 : forall rho b, TR (SPJ segsU (JGv tv0 (amh h1344c)) XFc2 rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_fail XFc2 [13%nat; 14%nat; 15%nat] Yc2 P_fail h1344c. Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using B1236 CVF ML POST REENTER TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. unfold exitsE in Hin. cbn [In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; injection H as <- <- <- <-.
  - apply X_E1.
  - apply X_E2.
  - apply X_E3.
  - apply B1236.
  - apply X_Fa1.
  - apply X_Fa2.
  - apply X_Fb1.
  - apply X_Fb2.
  - apply X_Fc1.
  - apply X_Fc2.
Qed.
End SumT.

Section Safety.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis VFS : S_vf.vf_stmt_U.
Hypothesis T1236 : fsB_stmt J1236 h1236.

Theorem fsB_sound : forall rho, triple segsU ok (SPJ segsU (JGv tv0 (amh fs_st.hJ852)) J rho) Q.
Proof using HS MC ML T1236 VFS.
  intros rho.
  apply (cfg_sound_JGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL cps 200 cutsE exitsE ok Q (proj1 HS)
           (ejcertA_jcertA segsU FD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
  apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
           (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
           (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @triple_ex segsU ok A P Q' H)
           (call_soundP segsU ok)).
  - intros FBc rho1. exact (VFS ok Kc FBc rho1 HS ML MC).
  - intros T tv am rT vT rho' b Hin _ _. exact (reenter_cutGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ok cutsE T tv am (rT, vT) Q rho' Hin).
  - intros P tv am rho' b Hin. apply (exit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB ok rho0 tv am (Posts_fs Kc FB) P). exact Hin.
  - intros rho' b. exact (@triple_conseq segsU ok _ _ _ _ (fun w Hw => Hw) (fun w Hw => or_intror Hw) (T1236 ok Kc FB rho0 rho' HS ML MC)).
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis VFX : S_vf.vf_ex_stmt_U.
Hypothesis X1236 : fsB_ex_stmt J1236 h1236.

Theorem fsB_complete : forall rho, etriple segsU (SPJ segsU (JGv tv0 (amh fs_st.hJ852)) J rho) Q.
Proof using Hvi MCX ML VFX X1236.
  intros rho.
  apply (cfg_complete_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL cps 200 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
  apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB) cutsE) b w \/ Q w)
           (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
           (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
           (fun A P Q' H => @etriple_ex segsU A P Q' H)
           (call_completeP segsU)).
  - intros FBc rho1. exact (VFX Kc FBc rho1 Hvi ML MCX).
  - intros T tv am rT vT rho' b Hin H0 Hb. apply (ereenter_cutAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB cutsE T tv am (rT, vT) Q b rho' Hin).
    unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho' vT)). nia.
  - intros P tv am rho' b Hin. apply (eexit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB rho0 tv am (Posts_fs Kc FB) P). exact Hin.
  - intros rho' b. exact (@etriple_conseq segsU _ _ _ _ (fun w Hw => Hw) (fun w Hw => or_intror Hw) (X1236 Kc FB rho0 rho' Hvi ML MCX)).
Qed.
End Existence.
End Sum.

Theorem fsB_sum_U : S_vf.vf_stmt_U -> fsB_stmt J1236 h1236 -> fsB_stmt fs_st.J852 fs_st.hJ852.
Proof. intros VFS T1236 ok Kc FB rho0 rho HS ML MC. exact (fsB_sound ok Kc FB rho0 ML HS MC VFS T1236 rho). Qed.

Theorem fsB_ex_U : S_vf.vf_ex_stmt_U -> fsB_ex_stmt J1236 h1236 -> fsB_ex_stmt fs_st.J852 fs_st.hJ852.
Proof. intros VFX X1236 Kc FB rho0 rho Hvi ML MCX. exact (fsB_complete Kc FB rho0 ML Hvi MCX VFX X1236 rho). Qed.
