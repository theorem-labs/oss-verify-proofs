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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_vf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vf_loop : Z := 0x158cc.
Definition FUEL_vf : nat := 300%nat.
Definition cutpcs_vf : list Z := [S_aa.aa_entry; vf_loop].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_vf cutpcs_vf S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_vf end.

Definition nC : sv := SMd M_MUL vE vC.
Definition mfact : sprop := SPUle nC (SLit two47).
Definition mfact2 : sprop := SPUle nC (kbytes vK).

Definition PreA : sstate := S_aa.Pre_aa 16.
Definition E_aa0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_vf S_aa.aa_entry) Pre_vf.
Definition E_aa : sstate := with_facts E_aa0 (mfact :: mfact2 :: ss_facts E_aa0).
Definition s_aa : wsub := (19%positive, dlo) :: infer_sub 10 E_aa PreA.
Definition R_aa : list sobj := Eval vm_compute in optR (entails_fr E_aa PreA s_aa).

Definition T_fail : sstate := Eval vm_compute in T_afterN NF E_aa s_aa R_aa S_aa.P_fail.
Definition T_ok : sstate := Eval vm_compute in T_afterN NF E_aa s_aa R_aa (S_aa.P_ok 16).
Definition am_fail : amode := Eval vm_compute in
  am_subst (import_sub s_aa NF S_aa.P_fail (ss_next E_aa)) (AHead S_aa.vHD).
Definition am_loop : amode := Eval vm_compute in
  am_subst (import_sub s_aa NF (S_aa.P_ok 16) (ss_next E_aa))
    (AOpen S_aa.vH S_aa.vNX S_aa.vCAP [(S_aa.vP, S_aa.vSZ)]).

Definition perm_ok : list nat := [5; 0; 1; 6; 2; 7; 3; 4]%nat.
Definition C_ok : sstate := Eval vm_compute in optS (apply_xforms T_ok [XSelect perm_ok]).

Definition X_loop0 : sstate := Eval vm_compute in nth 0 (leaves_at C_ok vf_loop) Pre_vf.
Definition vI : sv := SVar 145.
Definition C_loop : sstate := Eval vm_compute in
  mkSS vf_loop (setregs (ss_regs X_loop0) [(11%nat, vI)]) (ss_fregs X_loop0) (ss_fcsr X_loop0) (ss_resv X_loop0)
    (ss_objs X_loop0) (SPUlt vI nC :: ss_facts X_loop0) 146 false.

Definition X_ra : sstate := Eval vm_compute in nth 0 (leaves_at C_ok vf_ret) Pre_vf.
Definition X_rb : sstate := Eval vm_compute in nth 1 (leaves_at C_ok vf_ret) Pre_vf.
Definition X_rc : sstate := Eval vm_compute in nth 0 (leaves_at C_loop vf_ret) Pre_vf.

Definition is_data (o : sobj) : bool :=
  sv_eqb (ob_base o) vD && sv_eqb (ob_lo o) (SLit 0) && sv_eqb (ob_hi o) (kbytes vK).

Goal length (run_of Pre_vf) = 3%nat /\ length (run_of T_fail) = 3%nat /\ length (run_of C_ok) = 3%nat
  /\ length (run_of C_loop) = 2%nat /\ length (ss_objs C_ok) = 8%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma mfacts_hold : forall rho, Forall (holds rho) (ss_facts E_aa0) -> holds rho mfact /\ holds rho mfact2.
Proof using .
  intros rho HF.
  assert (H1 : holds rho (SPUle vC vK)) by (apply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  assert (H2 : holds rho (SPUle (kbytes vK) (SLit two47))) by (apply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  assert (H3 : holds rho (SPUle vK (SLit two47))) by (apply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  assert (H4 : holds rho (SPUle vE (SLit 4096))) by (apply (proj1 (Forall_forall _ _) HF); vm_compute; tauto).
  unfold mfact, mfact2, nC, kbytes in *. cbn [holds] in *. rewrite !U_mul in *. rewrite !U_lit in *.
  unfold vC, vK, vE in *. rewrite !eval_var in *. unfold M64v, two47 in *.
  pose proof (bv_urange (rw rho 16%positive)) as R6. pose proof (bv_urange (rw rho 17%positive)) as R7.
  pose proof (bv_urange (rw rho 18%positive)) as R8.
  rewrite (Z.mod_small 4096) in H4 by lia. rewrite (Z.mod_small (2 ^ 47)) in * by lia.
  rewrite Z.mod_small in H2 by nia. rewrite (Z.mod_small (bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 16%positive))) by nia.
  split; nia.
Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U NF Kc rho0 (P0_vf FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U NF Kc rho0 (P0_vf FB) FB tv am.
Let Q : assn := LQP segsU NF rho0 (Posts_vf Kc FB).

Definition z0 : sv := SLit 0.
Definition cp_var : sv := SAlu ALU_SUB nC vI.

Definition cutsE : list aedesc :=
  [ (Pre_vf, (tv0, ahd), (100, z0));
    (T_fail, (tv0, am_fail), (90, z0));
    (C_ok, (tv0, am_loop), (90, z0));
    (C_loop, (tv0, am_loop), (50, cp_var)) ].
Definition exitsE : list aedesc :=
  [ (E_aa0, (tv0, ahd), (95, z0));
    (X_ra, (tv0, am_loop), (10, z0));
    (X_rb, (tv0, am_loop), (10, z0));
    (X_rc, (tv0, am_loop), (10, z0));
    (P_zero, (tv0, ahd), (0, z0));
    (P_fail, (tv0, ahd), (0, z0));
    (P_ok, (tv0, am_ok), (0, z0)) ].

Lemma ejcert_ok : ejcertA segsU NF FUEL_vf cutpcs_vf 100 cutsE exitsE = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma P0_at : forall rho, agree_vals NF rho0 rho -> P0_vf FB rho0 -> P0_vf FB rho.
Proof using .
  intros rho Hav HP0.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E16 : rw rho 16%positive = rw rho0 16%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E17 : rw rho 17%positive = rw rho0 17%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E18 : rw rho 18%positive = rw rho0 18%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold P0_vf, kbytes, vE, vK in *. cbn [eval] in *. rewrite E15, E16, E17, E18. exact HP0.
Qed.

Lemma data_pclF : forall (R : list sobj) (facts : list sprop) (rho : valuation) (o : sobj) (a : Z),
  In o R -> is_data o = true -> P0_vf FB rho0 -> agree_vals NF rho0 rho -> Forall (holds rho) facts ->
  In (SPUle (kbytes vK) (SLit two47)) facts -> In (SPNot (SPBranch BC_EQ vC (SLit 0))) facts ->
  (fst (obj_range rho o) <= a /\ a < snd (obj_range rho o)) -> pclF segsU C_U rho0 FB a.
Proof using .
  intros R facts rho o a _ Ho HP0 Hav HF Hin Hnz Hr. unfold is_data in Ho.
  apply andb_prop in Ho as [Ho Hh]. apply andb_prop in Ho as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  pose proof (proj1 (Forall_forall _ _) HF _ Hnz) as HZ. apply (proj1 (holds_nbeq rho _ _)) in HZ.
  rewrite U_lit in HZ. unfold vC in HZ. rewrite eval_var in HZ.
  destruct (P0_at rho Hav HP0) as (b & n & Hbin & H1 & H2); [unfold M64v in HZ; rewrite Z.mod_small in HZ by lia; exact HZ |].
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HL. cbn [holds] in HL. rewrite U_lit in HL.
  unfold vD in *. rewrite !eval_var in *.
  unfold M64v, two47 in HL. rewrite Z.mod_small in HL by lia.
  destruct (Zsigned_spec (bv_unsigned (eval rho (kbytes vK)))) as [[_ X]|[X _]]; [|lia]. rewrite X in Hr.
  right; right. exists b, n. split; [exact Hbin | lia].
Qed.

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
Hypothesis CAA : forall (FBc : list (Z * Z)) (rho1 : valuation),
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_aa.P0_aa FBc) FBc S_aa.tv0 (AHead S_aa.vHD)) PreA rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_aa.P0_aa (S_aa.PDA_aa 16) FBc)).
Hypothesis REENTER : forall (T : sstate) (tv : list (sv * sv)) (am : amode) (rT : Z) (vT : sv) (rho : valuation) (b : Z),
  In ((T, (tv, am)), (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (am : amode) (rho : valuation) (b : Z),
  In (P, JLGA segsU C_U Kc (P0_vf FB) FB tv am) (Posts_vf Kc FB) ->
  TR (SPJ segsU (JGv tv am) P rho) (FAM b).

Let CALLAA := client_callAT segsU C_U NF Kc rho0 (P0_vf FB) FB ML S_aa.P0_aa PreA S_aa.tv0 (AHead S_aa.vHD)
  (S_aa.PDA_aa 16) NF (@eq_refl positive (ss_next PreA)) TR TR_facts TR_ex TR_pre TR_callP CAA.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <->
  (r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v)).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv am rT vT := apply (REENTER T tv am rT vT); [cbn; tauto | lia | first [lia | unfold ameas, ad_rank, ad_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_zero : forall rho b, TR (SPJ segsU (JGv tv0 ahd) P_zero rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0 ahd) P_fail rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_ok) P_ok rho) (FAM b).
Proof using POST. intros rho b. apply POST. cbn. tauto. Qed.

Ltac ret_ok X :=
  let rho := fresh "rho" in let b := fresh "b" in let w := fresh "w" in let Hw := fresh "Hw" in
  let rho1 := fresh "rho1" in let Hw1 := fresh "Hw1" in let rho2 := fresh "rho2" in let Hw2 := fresh "Hw2" in
  intros rho b;
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0 am_ok) P_ok r w)); [ | apply TR_exw; intros ?; apply X_P_ok ];
  intros w Hw;
  destruct (JGA_unslot segsU C_U NF Kc rho0 (P0_vf FB) FB ML tv0 (SVar 141) (SVar 142) (SVar 143) (SVar 140) nC
              X (firstn 7 (ss_objs X)) (nth 7 (ss_objs X) O_DD) rho w)
    as (rho1 & _ & Hw1); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw |];
  destruct (JGA_close segsU C_U NF Kc rho0 (P0_vf FB) FB ML tv0 (SVar 141) (SVar 142) (SVar 143) (SVar 144)
              (drop_last_state X (firstn 7 (ss_objs X))) (firstn 6 (firstn 7 (ss_objs X))) (nth 6 (ss_objs X) O_DD) rho1 w)
    as (rho2 & _ & Hw2); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw1 |];
  exists (rho_sub rho2 (infer_sub 100 (drop_last_state (drop_last_state X (firstn 7 (ss_objs X))) (firstn 6 (firstn 7 (ss_objs X)))) P_ok));
  eapply (SPJ_entails_JGA segsU C_U NF Kc rho0 (P0_vf FB) FB ML
            (drop_last_state (drop_last_state X (firstn 7 (ss_objs X))) (firstn 6 (firstn 7 (ss_objs X)))) P_ok
            (infer_sub 100 (drop_last_state (drop_last_state X (firstn 7 (ss_objs X))) (firstn 6 (firstn 7 (ss_objs X)))) P_ok)
            tv0 tv0 (AHead (SVar 141)) am_ok);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hw2].

Lemma X_ra_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_loop) X_ra rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_ok X_ra. Qed.
Lemma X_rb_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_loop) X_rb rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_ok X_rb. Qed.
Lemma X_rc_ok : forall rho b, TR (SPJ segsU (JGv tv0 am_loop) X_rc rho) (FAM b).
Proof using ML POST TR_exw TR_pre. ret_ok X_rc. Qed.

Lemma X_E_aa : forall rho, TR (SPJ segsU (JGv tv0 ahd) E_aa0 rho) (FAM (ameas ((E_aa0, (tv0, ahd)), (95, z0)) rho)).
Proof using CAA ML REENTER TR_callP TR_ex TR_facts TR_pre.
  intros rho. eapply TR_pre.
  2: { apply (CALLAA E_aa s_aa R_aa rho [] tv0 ahd).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF HP0 Hav HP HN HD HZ HXA HM HT. split; [| exact I].
    eapply (robjs_checkF_sound segsU C_U rho0 FB rho (ss_facts E_aa) [] is_data R_aa HF
              (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT)); [unfold tvz; constructor | vm_compute; reflexivity |].
    intros o a Ho Hx Hr. apply pclF_FBx.
    eapply (data_pclF R_aa (ss_facts E_aa) rho o a Ho Hx HP0 Hav HF); [vm_compute; tauto | vm_compute; tauto | exact Hr].
  - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
    + change (T_afterN NF E_aa s_aa R_aa S_aa.P_fail) with T_fail.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with tv0 by (vm_compute; reflexivity); replace am with am_fail by (vm_compute; reflexivity) end.
      reenter T_fail tv0 am_fail 90 z0.
    + change (T_afterN NF E_aa s_aa R_aa (S_aa.P_ok 16)) with T_ok.
      match goal with |- TR (SPJ _ (JGA _ _ _ _ _ _ _ ?tv ?am) _ _) _ =>
        replace tv with tv0 by (vm_compute; reflexivity); replace am with am_loop by (vm_compute; reflexivity) end.
      eapply TR_pre; [ | reenter C_ok tv0 am_loop 90 z0 ].
      intros w Hw. exact (SPJ_xforms segsU _ [XSelect perm_ok] rho' T_ok C_ok w ltac:(vm_compute; reflexivity) Hw). }
  intros w Hw. unfold E_aa. apply SPJ_refacts; [exact Hw | vm_compute; reflexivity |].
  intros HF. destruct (mfacts_hold rho HF) as [M1 M2]. constructor; [exact M1 | constructor; [exact M2 | exact HF]].
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof using CAA ML POST REENTER TR_callP TR_ex TR_exw TR_facts TR_pre.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; injection H as <- <- <- <-.
  - apply X_E_aa.
  - apply X_ra_ok.
  - apply X_rb_ok.
  - apply X_rc_ok.
  - apply X_P_zero.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Section Safety.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis AAS : S_aa.aa_stmt_U.

Theorem vf_sum : triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_vf FB) FB tv0 ahd) Pre_vf rho0)
  (LQP segsU NF rho0 (Posts_vf Kc FB)).
Proof using AAS HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segsU C_U NF Kc rho0 (P0_vf FB) FB ML FUEL_vf cutpcs_vf 100 cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros FBc rho1. exact (AAS 16 (or_intror eq_refl) ok Kc FBc rho1 HS ML MC).
       - intros T tv am rT vT rho b Hin _ _. exact (reenter_cutGAE segsU C_U NF Kc rho0 (P0_vf FB) FB ok cutsE T tv am (rT, vT) Q rho Hin).
       - intros P tv am rho b Hin. apply (exit_postGA segsU C_U NF Kc (P0_vf FB) FB ok rho0 tv am (Posts_vf Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis AAX : S_aa.aa_ex_stmt_U.

Theorem vf_sum_ex : etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_vf FB) FB tv0 ahd) Pre_vf rho0)
  (LQP segsU NF rho0 (Posts_vf Kc FB)).
Proof using AAX Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segsU C_U NF Kc rho0 (P0_vf FB) FB ML FUEL_vf cutpcs_vf 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U NF Kc rho0 (P0_vf FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros FBc rho1. exact (AAX 16 (or_intror eq_refl) Kc FBc rho1 Hvi ML MCX).
       - intros T tv am rT vT rho b Hin H0 Hb. apply (ereenter_cutAE segsU C_U NF Kc rho0 (P0_vf FB) FB cutsE T tv am (rT, vT) Q b rho Hin).
         unfold ameas, ad_rank, ad_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv am rho b Hin. apply (eexit_postGA segsU C_U NF Kc (P0_vf FB) FB rho0 tv am (Posts_vf Kc FB) P). exact Hin. }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem vf_sum_U : S_aa.aa_stmt_U -> vf_stmt_U.
Proof. intros AAS ok Kc FB rho0 HS ML MC. exact (vf_sum ok Kc FB rho0 HS ML MC AAS). Qed.

Theorem vf_ex_U : S_aa.aa_ex_stmt_U -> vf_ex_stmt_U.
Proof. intros AAX Kc FB rho0 Hvi ML MCX. exact (vf_sum_ex Kc FB rho0 ML Hvi MCX AAX). Qed.
