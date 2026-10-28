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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform TobjJV TobjArena TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require S_fsB.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import fs_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition kept0 : list (sv * sv) := Eval vm_compute in firstn 8 tv0.
Definition passed0 : list (sv * sv) := Eval vm_compute in skipn 8 tv0.
Lemma tv0_split : tv0 = kept0 ++ passed0.
Proof. vm_compute. reflexivity. Qed.

Lemma E_mi_eq : E_mi = with_facts E_mi0 (mfa 12 114 :: mfb 12 114 115 :: ss_facts E_mi0).
Proof. vm_compute. reflexivity. Qed.
Lemma E_fv_eq : E_fv = with_facts E_fv0 (mfa 4 117 :: mfb 4 117 118 :: ss_facts E_fv0).
Proof. vm_compute. reflexivity. Qed.
Lemma E_mm_eq : E_mm = with_facts E_mm0 (mfa 4 120 :: mfb 4 120 121 :: ss_facts E_mm0).
Proof. vm_compute. reflexivity. Qed.
Lemma E_sg_eq : E_sg = with_facts E_sg0 (mfa 4 123 :: mfb 4 123 124 :: ss_facts E_sg0).
Proof. vm_compute. reflexivity. Qed.

Lemma In_of_in_facts : forall (f : sprop) (l : list sprop), in_facts f l = true -> In f l.
Proof using .
  intros f l. induction l as [|g t IH]; cbn; intros H; [discriminate|].
  apply orb_true_iff in H as [H|H]; [left; symmetry; exact (sprop_eqb_sound _ _ H) | right; exact (IH H)].
Qed.

(* size facts for the arena_dup of a vector with element size e, count c, capacity k *)
Lemma mf_hold : forall (rho : valuation) (e : Z) (c k : positive) (facts : list sprop),
  0 < e <= 4096 ->
  in_facts (SPUle (SVar c) (SVar k)) facts = true ->
  in_facts (SPUle (SMd M_MUL (SLit e) (SVar k)) (SLit two47)) facts = true ->
  in_facts (SPUle (SVar k) (SLit two47)) facts = true ->
  Forall (holds rho) facts -> Forall (holds rho) (mfa e c :: mfb e c k :: facts).
Proof using .
  intros rho e c k facts He I1 I2 I3 HF.
  pose proof (proj1 (Forall_forall _ _) HF _ (In_of_in_facts _ _ I1)) as H1.
  pose proof (proj1 (Forall_forall _ _) HF _ (In_of_in_facts _ _ I2)) as H2.
  pose proof (proj1 (Forall_forall _ _) HF _ (In_of_in_facts _ _ I3)) as H3.
  assert (M : holds rho (mfa e c) /\ holds rho (mfb e c k)).
  { unfold mfa, mfb in *. cbn [holds] in *. rewrite !U_mul in *. rewrite !U_lit in *. rewrite !eval_var in *.
    unfold M64v, two47 in *.
    pose proof (bv_urange (rw rho c)) as Rc. pose proof (bv_urange (rw rho k)) as Rk.
    rewrite (Z.mod_small e) in * by lia. rewrite (Z.mod_small (2 ^ 47)) in * by lia.
    rewrite Z.mod_small in H2 by nia.
    rewrite (Z.mod_small (e * bv_unsigned (rw rho c))) by nia.
    rewrite (Z.mod_small (e * bv_unsigned (rw rho k))) by nia.
    split; nia. }
  destruct M as [M1 M2]. constructor; [exact M1 | constructor; [exact M2 | exact HF]].
Qed.

Definition am_parts (am : amode) : sv * sv * sv * sv * sv :=
  match am with AOpen h n c [(p, z)] => (h, n, c, p, z) | _ => (SLit 0, SLit 0, SLit 0, SLit 0, SLit 0) end.
Definition hdr_u (o : sobj) : sv :=
  match find (fun c => sveq (c_off c) (SLit 16)) (ob_cells o) with Some c => c_val c | None => SLit 0 end.

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

Lemma ejcert_ok : ejcertA segsU FD.NP FUEL_fs cutpcs_fs 200 cutsE exitsE = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

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
Hypothesis CAA : forall (al : Z), al = 1 \/ al = 16 -> forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_aa.P0_aa FBc) FBc S_aa.tv0 (AHead S_aa.vHD)) (S_aa.Pre_aa al) rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_aa.P0_aa (S_aa.PDA_aa al) FBc)).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_fs FB) FB tv am) (Posts_fs Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).
Hypothesis TAIL : forall (rho : valuation) (b : Z), TR (SPJ segsU (JGv tv0 (AHead (SVar hJ852))) J852 rho) (FAM b).

Let CALLAA (al : Z) (Hal : al = 1 \/ al = 16) :=
  client_callAT segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML S_aa.P0_aa (S_aa.Pre_aa al) S_aa.tv0 (AHead S_aa.vHD)
    (S_aa.PDA_aa al) NF (@eq_refl positive (ss_next (S_aa.Pre_aa al))) TR TR_facts TR_ex TR_pre TR_callP (CAA al Hal).

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac inlist := repeat first [left; reflexivity | right].
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT);
  [unfold cutsE; inlist | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_nop : forall rho b, TR (SPJ segsU (JGv tv0 ahd) P_nop rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0 amq) P_fail rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_failz : forall rho b, TR (SPJ segsU (JGv tv0 amq) P_failz rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.

(* continuations of an aa call: the failed and the successful return, objects back in Pre_fs order *)
Ltac aa_conts Cfl amf rf Cok amk rk :=
  let d := fresh "d" in let rho' := fresh "rho'" in let Hd := fresh "Hd" in let Hag := fresh "Hag" in
  intros d rho' Hd Hag; destruct Hd as [<-|[<-|[]]]; cbn [fst snd];
  match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) ?T _) _ =>
    replace tv with tv0 by (vm_compute; reflexivity) end;
  [ match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ _ ?am) ?T _) _ =>
      replace am with amf by (vm_compute; reflexivity);
      eapply TR_pre; [ | reenter Cfl tv0 amf rf z0 ];
      let w := fresh "w" in let Hw := fresh "Hw" in
      intros w Hw; exact (SPJ_xforms segsU _ [XSelect perm_fail] rho' T Cfl w ltac:(vm_compute; reflexivity) Hw) end
  | match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ _ ?am) ?T _) _ =>
      replace am with amk by (vm_compute; reflexivity);
      eapply TR_pre; [ | reenter Cok tv0 amk rk z0 ];
      let w := fresh "w" in let Hw := fresh "Hw" in
      intros w Hw; exact (SPJ_xforms segsU _ [XSelect perm_aa] rho' T Cok w ltac:(vm_compute; reflexivity) Hw) end ].

Ltac robjs E :=
  let Ai := fresh "Ai" in let ms := fresh "ms" in let HF := fresh "HF" in let HP0 := fresh "HP0" in
  let Hav := fresh "Hav" in let HP := fresh "HP" in let HN := fresh "HN" in let HD := fresh "HD" in
  let HZ := fresh "HZ" in let HXA := fresh "HXA" in let HM := fresh "HM" in let HT := fresh "HT" in
  intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT; split; [| exact I];
  apply (robjs_checkF_sound segsU C_U rho0 FB _ (ss_facts E) kept0 (fun _ => false) _ HF
           (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT));
  [ exact (proj1 (proj1 (Forall_app _ _ _) HZ)) | vm_compute; reflexivity |
    let o := fresh "o" in let a := fresh "a" in let Ho := fresh "Ho" in let Hx := fresh "Hx" in
    intros o a Ho Hx; discriminate Hx ].

Ltac call_side := vm_compute; reflexivity.

Lemma X_E_nm : forall rho, TR (SPJ segsU (JGv tv0 ahd) E_nm rho) (FAM (ameas ((E_nm, (tv0, ahd)), (96, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho. rewrite tv0_split.
  apply (CALLAA 1 (or_introl eq_refl) E_nm s_nm R_nm rho kept0 passed0 ahd);
    [call_side | call_side | call_side | call_side | call_side | call_side | call_side | call_side | call_side
    | robjs E_nm | ].
  aa_conts C_nm_fail am_nm_fail 94 C_nm_ok am_nm_ok 94.
Qed.

Ltac call_exit E0 E Eeq am rE Cfl amf rf Cok amk rk e c k :=
  let rho := fresh "rho" in
  intros rho; eapply TR_pre;
  [ | apply (CALLAA 16 (or_intror eq_refl) E (s_of E) (R_of E) rho kept0 passed0 am);
      [call_side | call_side | call_side | call_side | call_side | call_side | call_side | call_side | call_side
      | robjs E | aa_conts Cfl amf rf Cok amk rk ] ];
  let w := fresh "w" in let Hw := fresh "Hw" in
  intros w Hw; rewrite <- tv0_split, Eeq; apply SPJ_refacts; [exact Hw | vm_compute; reflexivity |];
  apply (mf_hold _ e c k); [lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].

Lemma X_E_mi : forall rho, TR (SPJ segsU (JGv tv0 (amJ J228)) E_mi0 rho) (FAM (ameas ((E_mi0, (tv0, amJ J228)), (90, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  call_exit E_mi0 E_mi E_mi_eq (amJ J228) 90 C_mi_fail am_mi_fail 88 C_mi_ok am_mi_ok 88 12 114%positive 115%positive.
Qed.
Lemma X_E_fv : forall rho, TR (SPJ segsU (JGv tv0 (amJ J404)) E_fv0 rho) (FAM (ameas ((E_fv0, (tv0, amJ J404)), (82, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  call_exit E_fv0 E_fv E_fv_eq (amJ J404) 82 C_fv_fail am_fv_fail 80 C_fv_ok am_fv_ok 80 4 117%positive 118%positive.
Qed.
Lemma X_E_mm : forall rho, TR (SPJ segsU (JGv tv0 (amJ J536)) E_mm0 rho) (FAM (ameas ((E_mm0, (tv0, amJ J536)), (74, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  call_exit E_mm0 E_mm E_mm_eq (amJ J536) 74 C_mm_fail am_mm_fail 72 C_mm_ok am_mm_ok 72 4 120%positive 121%positive.
Qed.
Lemma X_E_sg : forall rho, TR (SPJ segsU (JGv tv0 (amJ J672)) E_sg0 rho) (FAM (ameas ((E_sg0, (tv0, amJ J672)), (66, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  call_exit E_sg0 E_sg E_sg_eq (amJ J672) 66 C_sg_fail am_sg_fail 64 C_sg_ok am_sg_ok 64 4 123%positive 124%positive.
Qed.

(* a leaf reaching a join from an open-arena cut: drop the slot, close the arena, entail the join state *)
Ltac close_join X amX T rho :=
  let w := fresh "w" in let Hw := fresh "Hw" in
  let rho1 := fresh "rho1" in let Hw1 := fresh "Hw1" in let rho2 := fresh "rho2" in let Hw2 := fresh "Hw2" in
  let parts := eval vm_compute in (am_parts amX) in
  let n := eval vm_compute in (length (ss_objs X)) in
  let n1 := eval vm_compute in (n - 1)%nat in
  let n2 := eval vm_compute in (n - 2)%nat in
  match parts with (?h, ?nx, ?cap, ?p, ?z) =>
  let u := eval vm_compute in (hdr_u (nth n2 (ss_objs X) O_DD)) in
  let S1 := constr:(drop_last_state X (firstn n1 (ss_objs X))) in
  let L := constr:(drop_last_state S1 (firstn n2 (ss_objs X))) in
  intros w Hw;
  destruct (JGA_unslot segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML tv0 h nx cap p z X (firstn n1 (ss_objs X))
              (nth n1 (ss_objs X) O_DD) rho w)
    as (rho1 & _ & Hw1); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  destruct (JGA_close segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML tv0 h nx cap u S1 (firstn n2 (ss_objs X))
              (nth n2 (ss_objs X) O_DD) rho1 w)
    as (rho2 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                         | exact Hw1 |];
  exists (rho_sub rho2 (infer_sub 200 L T));
  exact (SPJ_entails_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML L T (infer_sub 200 L T)
           tv0 tv0 (AHead h) (amJ T) rho2 w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hw2)
  end.

Ltac close_exit X amX T rT :=
  let rho := fresh "rho" in let r := fresh "r" in
  intros rho;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 (amJ T)) T r w));
  [ close_join X amX T rho | apply TR_exw; intros r; reenter T tv0 (amJ T) rT z0 ].

Lemma X_nm228_ok : forall rho, TR (SPJ segsU (JGv tv0 am_nm_ok) X_nm228 rho) (FAM (ameas ((X_nm228, (tv0, am_nm_ok)), (93, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_nm228 am_nm_ok J228 92. Qed.
Lemma X_nm404_ok : forall rho, TR (SPJ segsU (JGv tv0 am_nm_ok) X_nm404 rho) (FAM (ameas ((X_nm404, (tv0, am_nm_ok)), (93, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_nm404 am_nm_ok J404 84. Qed.
Lemma X_mi_a_ok : forall rho, TR (SPJ segsU (JGv tv0 am_mi_ok) X_mi_a rho) (FAM (ameas ((X_mi_a, (tv0, am_mi_ok)), (87, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_mi_a am_mi_ok J404 84. Qed.
Lemma X_mi_b_ok : forall rho, TR (SPJ segsU (JGv tv0 am_mi_ok) X_mi_b rho) (FAM (ameas ((X_mi_b, (tv0, am_mi_ok)), (85, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_mi_b am_mi_ok J404 84. Qed.
Lemma X_fv_a_ok : forall rho, TR (SPJ segsU (JGv tv0 am_fv_ok) X_fv_a rho) (FAM (ameas ((X_fv_a, (tv0, am_fv_ok)), (79, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_fv_a am_fv_ok J536 76. Qed.
Lemma X_fv_b_ok : forall rho, TR (SPJ segsU (JGv tv0 am_fv_ok) X_fv_b rho) (FAM (ameas ((X_fv_b, (tv0, am_fv_ok)), (77, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_fv_b am_fv_ok J536 76. Qed.
Lemma X_mm_a_ok : forall rho, TR (SPJ segsU (JGv tv0 am_mm_ok) X_mm_a rho) (FAM (ameas ((X_mm_a, (tv0, am_mm_ok)), (71, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_mm_a am_mm_ok J672 68. Qed.
Lemma X_mm_b_ok : forall rho, TR (SPJ segsU (JGv tv0 am_mm_ok) X_mm_b rho) (FAM (ameas ((X_mm_b, (tv0, am_mm_ok)), (69, z0)) rho)).
Proof using ML REENTER TR_exw TR_pre. close_exit X_mm_b am_mm_ok J672 68. Qed.

Ltac close_tail X amX :=
  let rho := fresh "rho" in let r := fresh "r" in
  intros rho;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 (amJ J852)) J852 r w));
  [ close_join X amX J852 rho | apply TR_exw; intros r; exact (TAIL r _) ].
Lemma X_sg_a_ok : forall rho, TR (SPJ segsU (JGv tv0 am_sg_ok) X_sg_a rho) (FAM (ameas ((X_sg_a, (tv0, am_sg_ok)), (63, z0)) rho)).
Proof using ML TAIL TR_exw TR_pre. close_tail X_sg_a am_sg_ok. Qed.
Lemma X_sg_b_ok : forall rho, TR (SPJ segsU (JGv tv0 am_sg_ok) X_sg_b rho) (FAM (ameas ((X_sg_b, (tv0, am_sg_ok)), (61, z0)) rho)).
Proof using ML TAIL TR_exw TR_pre. close_tail X_sg_b am_sg_ok. Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using CAA ML POST REENTER TAIL TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]];
    injection H as <- <- <- <-.
  - apply X_E_nm.
  - apply X_nm228_ok.
  - apply X_nm404_ok.
  - apply X_E_mi.
  - apply X_mi_a_ok.
  - apply X_mi_b_ok.
  - apply X_E_fv.
  - apply X_fv_a_ok.
  - apply X_fv_b_ok.
  - apply X_E_mm.
  - apply X_mm_a_ok.
  - apply X_mm_b_ok.
  - apply X_E_sg.
  - apply X_sg_a_ok.
  - apply X_sg_b_ok.
  - apply TAIL.
  - apply X_P_nop.
  - apply X_P_fail.
  - apply X_P_failz.
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis AAS : S_aa.aa_stmt_U.
Hypothesis FSB : S_fsB.fsB_stmt J852 hJ852.

Theorem fs_sum : triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_fs FB) FB tv0 ahd) Pre_fs rho0) Q.
Proof using AAS FSB HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL_fs cutpcs_fs 200 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segsU FD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros al Hal FBc rho1. exact (AAS al Hal ok Kc FBc rho1 HS ML MC).
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB ok rho0 tv am (Posts_fs Kc FB) P). exact Hin.
       - intros rho b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
         exact (FSB ok Kc FB rho0 rho HS ML MC). }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis AAX : S_aa.aa_ex_stmt_U.
Hypothesis FSBX : S_fsB.fsB_ex_stmt J852 hJ852.

Theorem fs_sum_ex : etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_fs FB) FB tv0 ahd) Pre_fs rho0) Q.
Proof using AAX FSBX Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB ML FUEL_fs cutpcs_fs 200 cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros al Hal FBc rho1. exact (AAX al Hal Kc FBc rho1 Hvi ML MCX).
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segsU C_U FD.NP Kc rho0 (P0_fs FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segsU C_U FD.NP Kc (P0_fs FB) FB rho0 tv am (Posts_fs Kc FB) P). exact Hin.
       - intros rho b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
         exact (FSBX Kc FB rho0 rho Hvi ML MCX). }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem fs_sum_U : S_aa.aa_stmt_U -> S_fsB.fsB_stmt J852 hJ852 -> fs_stmt_U.
Proof. intros AAS FSB ok Kc FB rho0 HS ML MC. exact (fs_sum ok Kc FB rho0 HS ML MC AAS FSB). Qed.

Theorem fs_ex_U : S_aa.aa_ex_stmt_U -> S_fsB.fsB_ex_stmt J852 hJ852 -> fs_ex_stmt_U.
Proof. intros AAX FSBX Kc FB rho0 Hvi ML MCX. exact (fs_sum_ex Kc FB rho0 ML Hvi MCX AAX FSBX). Qed.
