From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_ra.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ra_L : Z := 0x1c224.
Definition FUEL_ra : nat := 400%nat.
Definition cutpcs_ra : list Z := [ra_L; ec_malloc EC_U; ec_free EC_U].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_ra cutpcs_ra S true with Some ls => map lf_state ls | None => [] end.
Definition leaf_k (S : sstate) (k : nat) : sstate := nth k (run_of S) Pre_ra.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : sstate := Eval vm_compute in leaf_k Pre_ra 0.
Definition s_m : wsub := (15%positive, vDp) :: infer_sub 10 E_m (Pre_malloc EC_U).
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_U) s_m).

Definition vR : positive := 110.
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_U).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_U).
Definition T_mok : sstate := add_facts (tv_facts (SVar vR, vNS)) T_mok0.

Definition L_os : sstate := Eval vm_compute in leaf_k T_mok 0.
Definition vI : sv := SVar 150.  Definition vN : sv := SVar 151.
Definition C_L : sstate := Eval vm_compute in
  mkSS ra_L (setregs (ss_regs L_os)
              [(13%nat, vN); (14%nat, vI); (5%nat, SVar 152); (6%nat, SVar 153); (7%nat, SVar 154);
               (17%nat, SVar 155); (28%nat, SVar 156); (29%nat, SVar 157); (30%nat, SVar 158); (31%nat, SVar 159)])
    pre_fregs FcsrFrm0 None (ss_objs L_os)
    ([SPUlt vI vN; SPUle vN vOS; SPUle vN vNS; SPUle vN (SLit hiA);
      SPUle (SAlu ALU_ADD (SVar vR) vN) (SLit hiA); SPUle (SAlu ALU_ADD vP vN) (SLit hiA)] ++ tl (ss_facts L_os))
    160 false.

Definition E_f : sstate := Eval vm_compute in leaf_k C_L 1.
Definition s_f : wsub := (15%positive, vDp) :: (13%positive, vOS) :: infer_sub 10 E_f (Pre_free EC_U).
Definition R_f : list sobj := Eval vm_compute in optR (entails_fr E_f (Pre_free EC_U) s_f).
Definition T_free : sstate := Eval vm_compute in T_after E_f s_f R_f (L_free EC_U).

Definition tv_m : list (sv * sv) := [(SVar vR, vNS); (vP, vOS)].
Definition tv_f : list (sv * sv) := [(SVar vR, vNS)].

Definition z0 : sv := SLit 0.
Definition cp_var : sv := SAlu ALU_SUB vN vI.
Definition cutsE : list edesc :=
  [(Pre_ra, tv0, (100, z0)); (T_mnull, tv0, (80, z0)); (T_mok, tv_m, (80, z0));
   (C_L, tv_m, (70, cp_var)); (T_free, tv_f, (60, z0))].
Definition exitsE : list edesc :=
  [(E_m, tv0, (90, z0)); (E_f, tv_m, (65, z0)); (P_fail, tv0, (0, z0)); (P_ok, tvP, (0, z0))].

Lemma ejcert_ok : ejcert segsU NF FUEL_ra cutpcs_ra 100 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma call_m_ok : call_checkT C_U NF E_m (Pre_malloc EC_U) s_m R_m [L_malloc_null EC_U; L_malloc_ok EC_U] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma call_f_ok : call_checkT C_U NF E_f (Pre_free EC_U) s_f R_f [L_free EC_U] = true.
Proof. vm_compute. reflexivity. Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : sstate * list (sv * sv) -> jnode := nodeI segsU C_U NF Kc rho0 P0_ra FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 P0_ra FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_ra Kc FB).

Lemma robjs_nil : forall Ai x rho, robjs_ok segsU C_U Ai x rho [].
Proof. intros Ai x rho o a Ho. destruct Ho. Qed.
Lemma robjs_cons : forall Ai x rho o R,
  (forall a, fst (obj_range rho o) <= a < snd (obj_range rho o) -> caddr segsU C_U Ai x a) ->
  robjs_ok segsU C_U Ai x rho R -> robjs_ok segsU C_U Ai x rho (o :: R).
Proof. intros Ai x rho o R Ho HR o' a [<-|Hin] Hr; [exact (Ho a Hr) | exact (HR o' a Hin Hr)]. Qed.

Lemma stack_obj_caddr : forall Ai x rho b lo hi cells d,
  - 2 ^ 63 <= lo < 2 ^ 63 -> - 2 ^ 63 <= hi < 2 ^ 63 ->
  T_ok rho (topL (ma_L Ai)) ->
  bv_unsigned (rw rho 30%positive) <= bv_unsigned (eval rho b) + lo ->
  forall a, fst (obj_range rho (mkObj b (SLit lo) (SLit hi) cells d)) <= a <
            snd (obj_range rho (mkObj b (SLit lo) (SLit hi) cells d)) -> caddr segsU C_U Ai x a.
Proof.
  intros Ai x rho b lo hi cells d Hlo Hhi [HT _] Hb a Hr. left. unfold V_TOP in HT. rewrite <- HT.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma block_obj_caddr : forall Ai x rho b hi cells d bb n,
  bv_unsigned (eval rho b) = bb ->
  (0 < Zsigned (bv_unsigned (eval rho hi)) ->
     In (bb, n) (ma_blocks Ai) /\ x <> Some bb /\ Zsigned (bv_unsigned (eval rho hi)) <= n) ->
  forall a, fst (obj_range rho (mkObj b (SLit 0) hi cells d)) <= a <
            snd (obj_range rho (mkObj b (SLit 0) hi cells d)) -> caddr segsU C_U Ai x a.
Proof.
  intros Ai x rho b hi cells d bb n Hb H a Hr. right; right.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U, Hb in Hr.
  destruct (H ltac:(lia)) as (Hin & Hx & Hn). exists bb, n. split; [exact Hin|]. split; [exact Hx|]. lia.
Qed.

Lemma tnz_var : forall rho v sz, tnz rho (SVar v, sz) <-> bv_unsigned (rw rho v) <> 0.
Proof. intros. unfold tnz. cbn [fst eval]. tauto. Qed.

Lemma old_blk_ok : forall rho Ai tv x,
  holds rho (SPUle (SLit 4096) vP) -> holds rho (SPUle vOS (SLit hiA)) ->
  tvin FB Ai rho tv -> In (vP, vOS) tv -> x <> Some (bv_unsigned (rw rho 13%positive)) ->
  forall a, fst (obj_range rho (O_blk vP vOS)) <= a < snd (obj_range rho (O_blk vP vOS)) -> caddr segsU C_U Ai x a.
Proof.
  intros rho Ai tv x H1 H2 HN Hin Hx.
  assert (Hnz : bv_unsigned (rw rho 13%positive) <> 0) by (unfold vP in H1; zfacts; lia).
  destruct (proj1 (Forall_forall _ _) HN _ Hin (proj2 (tnz_var rho _ _) Hnz)) as (_ & X & _).
  unfold tvv in X. cbn [fst snd] in X. unfold vP, vOS in X. rewrite !eval_var in X.
  eapply (block_obj_caddr Ai x rho vP vOS [] DUnknown _ (bv_unsigned (rw rho 14%positive))); [unfold vP; rewrite eval_var; reflexivity|].
  intros _. split; [exact X|]. split; [exact Hx|].
  unfold vOS. rewrite eval_var. unfold vOS, hiA, S_vr.hiA in H2.
  destruct (Zsigned_spec (bv_unsigned (rw rho 14%positive))) as [[_ E]|[_ E]]; rewrite E;
    pose proof (bv_urange (rw rho 14%positive)); zfacts; lia.
Qed.

Lemma R_m_ok : forall rho Ai tv,
  Forall (holds rho) (ss_facts E_m) -> tvin FB Ai rho tv -> In (vP, vOS) tv ->
  T_ok rho (topL (ma_L Ai)) -> robjs_ok segsU C_U Ai None rho R_m.
Proof.
  intros rho Ai tv HF HN Hin HT.
  pick_facts HF [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 8%nat; 11%nat; 13%nat].
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]].
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN Hin. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN Hin. zfacts; lia.
  - eapply (old_blk_ok rho Ai tv); try eassumption. discriminate.
Qed.

Lemma R_f_ok : forall rho Ai,
  Forall (holds rho) (ss_facts E_f) -> tvin FB Ai rho tv_m -> tvd rho tv_m ->
  (exists rhoM md, MInvR segsU C_U Ai rhoM md) -> T_ok rho (topL (ma_L Ai)) ->
  robjs_ok segsU C_U Ai (Some (bv_unsigned (rw rho 13%positive))) rho R_f.
Proof.
  intros rho Ai HF HN HD (rhoM & md & HM) HT.
  pick_facts HF [7%nat; 10%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 20%nat; 23%nat; 25%nat].
  assert (Hn : bv_unsigned (rw rho vR) <> 0) by (unfold vR in *; zfacts; lia).
  assert (Hd : bv_unsigned (rw rho 13%positive) <> 0) by (zfacts; lia).
  destruct (proj1 (Forall_forall _ _) HN (SVar vR, vNS) ltac:(left; reflexivity) (proj2 (tnz_var rho _ _) Hn)) as (Npos & NinA & _).
  destruct (proj1 (Forall_forall _ _) HN (vP, vOS) ltac:(right; left; reflexivity) (proj2 (tnz_var rho _ _) Hd)) as (Dpos & DinA & _).
  unfold tvv in NinA, DinA, Npos, Dpos. cbn [fst snd] in NinA, DinA, Npos, Dpos. unfold vP, vOS, vNS in *. rewrite !eval_var in NinA, DinA, Npos, Dpos.
  assert (Hne : bv_unsigned (rw rho vR) <> bv_unsigned (rw rho 13%positive)).
  { destruct HD as [HD1 _]. specialize (HD1 (vP, vOS) ltac:(left; reflexivity)
      (proj2 (tnz_var rho _ _) Hn) (proj2 (tnz_var rho _ _) Hd)).
    unfold tvv in HD1. cbn [fst snd] in HD1. unfold vP, vOS, vNS in HD1. rewrite !eval_var in HD1.
    eapply (blocks_bases_differ segsU C_U Ai rhoM md); eauto. }
  apply robjs_cons; [|apply robjs_cons; [|apply robjs_cons; [|apply robjs_nil]]].
  - eapply (block_obj_caddr Ai (Some _) rho (SVar vR) (SVar 33) _ DUnknown (bv_unsigned (rw rho vR)) (bv_unsigned (rw rho 33%positive)));
      [rewrite eval_var; reflexivity|].
    intros _. split; [exact NinA|]. split; [congruence|]. rewrite eval_var.
    destruct (Zsigned_spec (bv_unsigned (rw rho 33%positive))) as [[_ X]|[_ X]]; rewrite X; pose proof (bv_urange (rw rho 33%positive)); lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. zfacts; lia.
  - apply stack_obj_caddr; [cbn; lia | cbn; lia | exact HT |]. pose proof (TobjJVx.T_ok_range30 _ _ HT) as HT30.
    rewrite eval_var. clear HN HD HM NinA DinA Hne Npos Dpos Hd Hn. zfacts; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
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
     smatch segsU rhoL L (tr', mkCfg ms' md') ->
     JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.

Hypothesis CMALLOC : forall Ai rho1,
  TR (SPJ segsU (J_alloc_pre segsU C_U Ai Kc) (Pre_malloc EC_U) rho1) (LQP segsU NF rho1 (Posts_malloc segsU C_U EC_U Ai Kc)).
Hypothesis CFREE : forall Ai rho1,
  TR (SPJ segsU (J_free_pre segsU C_U Ai Kc) (Pre_free EC_U) rho1) (LQP segsU NF rho1 [(L_free EC_U, JL_free segsU C_U Ai Kc)]).
Hypothesis REENTER : forall T tv rT vT rho b,
  In (T, tv, (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc P0_ra FB tv) (Posts_ra Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let MALLOC := malloc_callT segsU C_U EC_U NF Kc rho0 P0_ra FB ML TR TR_facts TR_ex TR_pre TR_callP.
Let FREE := free_callT segsU C_U EC_U NF Kc rho0 P0_ra FB ML TR TR_facts TR_ex TR_pre TR_callP.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <-> r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v).
Proof. intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia].

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0) P_fail rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_ok : forall rho b, TR (SPJ segsU (JGv tvP) P_ok rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_m : forall rho, TR (SPJ segsU (JGv tv0) E_m rho) (FAM (emeas (E_m, tv0, (90, z0)) rho)).
Proof.
  intros rho.
  apply (MALLOC E_m s_m R_m rho tv0 _ CMALLOC).
  - vm_compute. reflexivity.
  - exact call_m_ok.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT. split.
    + exact (R_m_ok rho Ai tv0 HF HN ltac:(left; reflexivity) HT).
    + change (wsub_get s_m 12) with vNS. pick_facts HF [15%nat; 16%nat]. unfold vNS, vOS in *. zfacts; lia.
  - intros rho'.
    replace (T_after E_m s_m R_m (L_malloc_null EC_U)) with T_mnull by (vm_compute; reflexivity).
    reenter T_mnull tv0 80.
  - intros rho'.
    replace (T_after E_m s_m R_m (L_malloc_ok EC_U)) with T_mok0 by (vm_compute; reflexivity).
    change (pos_add_nat (ss_next E_m) 10) with vR. change (wsub_get s_m 12) with vNS.
    eapply TR_pre; [ | reenter T_mok tv_m 80 ].
    intros w Hw. unfold T_mok. apply SPJ_refacts_J; [exact Hw | reflexivity |].
    intros tr md HJ HF.
    eapply (JG_tv_facts segsU C_U NF Kc rho0 P0_ra FB); [exact HJ | left; reflexivity |].
    apply tnz_of_fact. pick_facts HF [18%nat]. assumption.
Qed.

Lemma X_E_f : forall rho, TR (SPJ segsU (JGv tv_m) E_f rho) (FAM (emeas (E_f, tv_m, (65, z0)) rho)).
Proof.
  intros rho.
  apply (FREE E_f s_f R_f rho tv_m 1%nat (vP, vOS) _ CFREE).
  - vm_compute. reflexivity.
  - exact call_f_ok.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros Ai HF HP0 Hav HP HN HD HZ HM HT.
    change (wsub_get s_f 12) with vP. change (wsub_get s_f 13) with vOS.
    split; [|split; [reflexivity|]].
    + unfold vP. apply (proj2 (tnz_var rho 13%positive vOS)). pick_facts HF [23%nat]. zfacts; lia.
    + unfold vP at 1. rewrite eval_var. exact (R_f_ok rho Ai HF HN HD HM HT).
  - intros rho'.
    replace (T_after E_f s_f R_f (L_free EC_U)) with T_free by (vm_compute; reflexivity).
    reenter T_free tv_f 60.
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_m.
  - apply X_E_f.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End SumT.

Theorem ra_sum_S : triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_ra FB tv0) Pre_ra rho0) Q.
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 P0_ra FB ML FUEL_ra cutpcs_ra 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_soundP segsU ok)).
       - intros Ai rho1. apply (mc_malloc _ _ _ MC). exact HS.
       - intros Ai rho1. apply (mc_free _ _ _ MC). exact HS.
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segsU C_U NF Kc rho0 P0_ra FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc P0_ra FB ok rho0 tv (Posts_ra Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.

Theorem ra_sum_E : etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_ra FB tv0) Pre_ra rho0) Q.
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 P0_ra FB ML FUEL_ra cutpcs_ra 100 cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 P0_ra FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_completeP segsU)).
       - intros Ai rho1. apply (mcx_malloc _ _ _ MCX). exact Hvi.
       - intros Ai rho1. apply (mcx_free _ _ _ MCX). exact Hvi.
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segsU C_U NF Kc rho0 P0_ra FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc P0_ra FB rho0 tv (Posts_ra Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem ra_sum : ra_stmt_U.
Proof. intros ok Kc FB rho0 HS ML MC. apply ra_sum_S; assumption. Qed.

Theorem ra_sum_ex : ra_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi ML MCX. apply ra_sum_E; assumption. Qed.
