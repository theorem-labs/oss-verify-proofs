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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue TobjJV ObjUnbase ObjXform.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_vr S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* vec_push (vp) on the ubsan image: vr call, then the slot d + esz*count is zeroed by an inlined byte loop
   (head vp_L) instead of P's memset call. The slot is carved out of the data object right after vr returns,
   so the loop's stores land in their own object; at the return the slot is merged back (P's mid_obj). *)
Module PV := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_push.

Definition z0 : sv := SLit 0.
Definition FUEL_vp : nat := 200%nat.
Definition vp_L : Z := vp_entry + 104.
Definition cutpcs_vp : list Z := [vr_entry; vp_L].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_vp cutpcs_vp S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_vp end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition xs_vr : list xform := [XSplit 1 (SLit (-32))].
Definition E_vr0 : sstate := Eval vm_compute in nth 0 (leaves_at Pre_vp vr_entry) Pre_vp.
Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr0 xs_vr).
Definition E_vr : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-32)).
Definition s_vr : wsub := Eval vm_compute in
  [(19%positive, SAlu ALU_ADD vDp (SLit 32)); (15%positive, vD); (16%positive, vC); (17%positive, vK);
   (18%positive, vE)] ++ infer_sub 10 E_vr Pre_vr.
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr Pre_vr s_vr).
Definition T_keep0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_keep.
Definition T_fail0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_fail.
Definition T_grown0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr P_grown.

Definition slot_facts (K : sv) : list sprop :=
  [SPUle (kbytes vC) (kbytes K); SPUle (SAlu ALU_ADD (kbytes vC) vE) (kbytes K)].
Definition xs_carve (i : nat) : list xform :=
  [XSplit i (kbytes vC); XSplit (Datatypes.S i) (SAlu ALU_ADD (kbytes vC) vE)].
Definition slot_obj (d : sv) : sobj := mkObj (SAlu ALU_ADD d (kbytes vC)) (SLit 0) vE [] DUnknown.
Definition mid_obj (d : sv) : sobj := mkObj d (kbytes vC) (SAlu ALU_ADD (kbytes vC) vE) [] DUnknown.

Definition T_keep1 : sstate := add_facts (slot_facts vK) T_keep0.
Definition T_keep2 : sstate := Eval vm_compute in optS (apply_xforms T_keep1 (xs_carve 4)).
Definition T_keep3 : sstate := reshape_obj_at T_keep2 5 (slot_obj vD).
Definition T_keepC : sstate := Eval vm_compute in add_facts (tv_facts (vD, kbytes vK)) T_keep3.
Definition T_grown1 : sstate := add_facts (slot_facts vKn) T_grown0.
Definition T_grown2 : sstate := Eval vm_compute in optS (apply_xforms T_grown1 (xs_carve 1)).
Definition T_grownC : sstate := Eval vm_compute in reshape_obj_at T_grown2 2 (slot_obj vDn).

(* Loop head vp_L: a2 = byte index vI < esz, a4 = the previous store address (dead). *)
Definition vI : sv := SVar 150.
Definition loop_cut (L : sstate) : sstate :=
  mkSS vp_L (setregs (ss_regs L) [(12%nat, vI); (14%nat, SVar 151)]) (ss_fregs L) (ss_fcsr L) (ss_resv L)
    (ss_objs L) (SPUlt vI vE :: ss_facts L) 152 (ss_lenient L).
Definition C_Lk : sstate := Eval vm_compute in loop_cut (nth 0 (leaves_at T_keepC vp_L) Pre_vp).
Definition C_Lg : sstate := Eval vm_compute in loop_cut (nth 0 (leaves_at T_grownC vp_L) Pre_vp).

Definition X_fail : sstate := Eval vm_compute in nth 0 (leaves_at T_fail0 vp_ret) Pre_vp.
Definition X_keep : sstate := Eval vm_compute in nth 0 (leaves_at C_Lk vp_ret) Pre_vp.
Definition X_grown : sstate := Eval vm_compute in nth 0 (leaves_at C_Lg vp_ret) Pre_vp.

Definition xs_f : list xform := [XRebase 0; XRebase 1; XSelect [1; 0; 2; 3; 4; 5]%nat; XMerge 0].
Definition X_fail2 : sstate := Eval vm_compute in optS (apply_xforms X_fail xs_f).
Definition X_fail3 : sstate := Eval vm_compute in optS (unbase_obj_at X_fail2 0 (-16)).
Definition s_xf : wsub := Eval vm_compute in infer_sub 100 X_fail3 P_push_fail.
Definition X_keep1 : sstate := reshape_obj_at X_keep 5 (mid_obj vD).
Definition xs_k : list xform := [XMerge 4; XMerge 4; XRebase 0; XRebase 1; XSelect [1; 0; 4; 2; 3; 5]%nat; XMerge 0].
Definition X_keep2 : sstate := Eval vm_compute in optS (apply_xforms X_keep1 xs_k).
Definition X_keep3 : sstate := Eval vm_compute in optS (unbase_obj_at X_keep2 0 (-16)).
Definition s_xk : wsub := Eval vm_compute in infer_sub 100 X_keep3 P_push_keep.
Definition X_grown1 : sstate := reshape_obj_at X_grown 2 (mid_obj vDn).
Definition xs_g : list xform := [XMerge 1; XMerge 1; XRebase 0; XRebase 2; XSelect [0; 2; 1; 3; 4; 5]%nat; XMerge 0].
Definition X_grown2 : sstate := Eval vm_compute in optS (apply_xforms X_grown1 xs_g).
Definition X_grown3 : sstate := Eval vm_compute in optS (unbase_obj_at X_grown2 0 (-16)).
Definition s_xg : wsub := Eval vm_compute in infer_sub 100 X_grown3 P_push_grown.

Definition cutsE : list edesc :=
  [(Pre_vp, tv0, (100, z0)); (T_fail0, tv0, (80, z0)); (T_keepC, tv0, (80, z0)); (T_grownC, tv_post, (80, z0));
   (C_Lk, tv0, (50, SAlu ALU_SUB vE vI)); (C_Lg, tv_post, (50, SAlu ALU_SUB vE vI))].
Definition exitsE : list edesc :=
  [(E_vr0, tv0, (90, z0)); (X_fail, tv0, (0, z0)); (X_keep, tv0, (0, z0)); (X_grown, tv_post, (0, z0))].

Lemma ejcert_ok : ejcert segsU NF FUEL_vp cutpcs_vp 100 cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma fact_in : forall rho (l : list sprop) p, Forall (holds rho) l -> In p l -> holds rho p.
Proof. intros rho l p H Hin. exact (proj1 (Forall_forall _ _) H p Hin). Qed.
Ltac getf HF p H := pose proof (fact_in _ _ p HF ltac:(vm_compute; tauto)) as H.

Lemma ule_lit : forall rho x c, holds rho (SPUle x (SLit c)) -> 0 <= c < M64v -> bv_unsigned (eval rho x) <= c.
Proof. intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.
Ltac ule_from H := exact (ule_lit _ _ _ H ltac:(unfold M64v, two47, hiA; lia)).
Ltac ule47 H := eapply Z.le_trans; [exact (ule_lit _ _ _ H ltac:(unfold M64v, two47, hiA; lia)) | unfold two47, hiA; lia].

(* esz * cap >= 1 when esz >= 1 and count + 1 <= cap <= 2^47. *)
Lemma kK_pos : forall rho, holds rho (SPUle (SLit 1) vE) -> holds rho (SPUle vE (SLit 4096)) ->
  holds rho (SPUle vC vK) -> holds rho (SPUle (SAlu ALU_ADD vC (SLit 1)) vK) -> holds rho (SPUle vK (SLit two47)) ->
  1 <= bv_unsigned (eval rho (kbytes vK)).
Proof.
  intros rho He1 He2 HcK Hc HK.
  apply ule_lit in He2; [|unfold M64v; lia]. apply ule_lit in HK; [|unfold M64v, two47; lia].
  cbn [holds] in He1, HcK, Hc. rewrite U_lit in He1. rewrite U_add, U_lit in Hc.
  unfold kbytes, vE, vC, vK in *. rewrite U_mul. rewrite !eval_var in *.
  pose proof (bv_urange (rw rho 16%positive)) as R16. pose proof (bv_urange (rw rho 17%positive)) as R17.
  pose proof (bv_urange (rw rho 18%positive)) as R18. unfold M64v, two47 in *.
  rewrite (Z.mod_small 1) in He1, Hc by lia.
  rewrite (Z.mod_small (_ + 1)) in Hc by lia.
  assert (0 <= bv_unsigned (rw rho 18%positive) * bv_unsigned (rw rho 17%positive) <= 4096 * 2 ^ 47) by nia.
  rewrite Z.mod_small by lia. nia.
Qed.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <-> r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v).
Proof. intros. pose proof (urange (eval rho v)). nia. Qed.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : sstate * list (sv * sv) -> jnode := nodeI segsU C_U NF Kc rho0 P0_vr FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 P0_vr FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_vp Kc FB).

Lemma P0_vr_at : forall rho, agree_vals NF rho0 rho -> P0_vr rho0 -> P0_vr rho.
Proof.
  intros rho Hav H. unfold P0_vr in *.
  assert (E15 : rw rho 15%positive = rw rho0 15%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  assert (E17 : rw rho 17%positive = rw rho0 17%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  rewrite E15, E17. exact H.
Qed.

(* The data block of a nonempty vector is a live block: tv_facts of (vD, esz * cap). *)
Lemma tv0_facts : forall rho tr md, JGv tv0 rho tr md -> 1 <= bv_unsigned (eval rho (kbytes vK)) ->
  Forall (holds rho) (tv_facts (vD, kbytes vK)).
Proof.
  intros rho tr md HJ Hk.
  assert (Hnz : tnz rho (vD, kbytes vK)).
  { intros Hz0. pose proof HJ as (Ai & _ & _ & _ & _ & (_ & _ & HZ) & _).
    pose proof (proj1 (Forall_forall _ _) HZ _ (or_introl eq_refl) (fun X => X Hz0)) as Z0.
    unfold tvv in Z0. cbn [snd] in Z0. lia. }
  exact (JG_tv_facts segsU C_U NF Kc rho0 P0_vr FB tv0 rho tr md _ HJ (or_introl eq_refl) Hnz).
Qed.

Lemma keepC_ok : forall rho w, SPJ segsU (JGv tv0) T_keep0 rho w -> SPJ segsU (JGv tv0) T_keepC rho w.
Proof.
  intros rho w Hw.
  assert (W1 : SPJ segsU (JGv tv0) T_keep1 rho w).
  { unfold T_keep1. apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
    intros tr md _ HF.
    getf HF (SPUle (SAlu ALU_ADD vC (SLit 1)) vK) Hc. getf HF (SPUle (SLit 1) vE) He1.
    getf HF (SPUle vE (SLit 4096)) He2. getf HF (SPUle vK (SLit two47)) HK. getf HF (SPUle vC vK) HcK.
    apply (PV.slot_facts_ok rho vK Hc He1 He2); [ule_from HK|].
    cbn [holds] in HcK. eapply Z.le_trans; [exact HcK | ule_from HK]. }
  assert (W2 : SPJ segsU (JGv tv0) T_keep2 rho w)
    by exact (SPJ_xforms segsU _ (xs_carve 4) rho T_keep1 T_keep2 w ltac:(vm_compute; reflexivity) W1).
  assert (W3 : SPJ segsU (JGv tv0) T_keep3 rho w).
  { unfold T_keep3. eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact W2].
    intros HF.
    getf HF (SPUle (kbytes vC) (kbytes vK)) Ha. getf HF (SPUle (SAlu ALU_ADD (kbytes vC) vE) (kbytes vK)) Hb.
    getf HF (SPUle (kbytes vK) (SLit two47)) H1. getf HF (SPUle vD (SLit two47)) H2. getf HF (SPUle vE (SLit 4096)) H3.
    unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi slot_obj].
    exact (PV.slot_range_eqs rho vD vK Ha Hb ltac:(ule_from H1) ltac:(ule_from H2) ltac:(ule_from H3)). }
  replace T_keepC with (add_facts (tv_facts (vD, kbytes vK)) T_keep3) by (vm_compute; reflexivity).
  apply SPJ_refacts_J; [exact W3 | vm_compute; reflexivity |].
  intros tr md HJ HF. apply (tv0_facts rho tr md HJ).
  getf HF (SPUle (SAlu ALU_ADD vC (SLit 1)) vK) Hc. getf HF (SPUle (SLit 1) vE) He1.
  getf HF (SPUle vE (SLit 4096)) He2. getf HF (SPUle vK (SLit two47)) HK. getf HF (SPUle vC vK) HcK.
  exact (kK_pos rho He1 He2 HcK Hc HK).
Qed.

Lemma grownC_ok : forall rho w, SPJ segsU (JGv tv_post) T_grown0 rho w -> SPJ segsU (JGv tv_post) T_grownC rho w.
Proof.
  intros rho w Hw.
  assert (W1 : SPJ segsU (JGv tv_post) T_grown1 rho w).
  { unfold T_grown1. apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
    intros tr md _ HF.
    getf HF (SPUle (SAlu ALU_ADD vC (SLit 1)) vKn) Hc. getf HF (SPUle (SLit 1) vE) He1.
    getf HF (SPUle vE (SLit 4096)) He2. getf HF (SPUle vKn (SLit hiA)) HKn.
    getf HF (SPUle vK (SLit two47)) HK. getf HF (SPUle vC vK) HcK.
    apply (PV.slot_facts_ok rho vKn Hc He1 He2); [ule47 HKn|].
    cbn [holds] in HcK. eapply Z.le_trans; [exact HcK | ule_from HK]. }
  assert (W2 : SPJ segsU (JGv tv_post) T_grown2 rho w)
    by exact (SPJ_xforms segsU _ (xs_carve 1) rho T_grown1 T_grown2 w ltac:(vm_compute; reflexivity) W1).
  replace T_grownC with (reshape_obj_at T_grown2 2 (slot_obj vDn)) by (vm_compute; reflexivity).
  eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact W2].
  intros HF.
  getf HF (SPUle (kbytes vC) (kbytes vKn)) Ha. getf HF (SPUle (SAlu ALU_ADD (kbytes vC) vE) (kbytes vKn)) Hb.
  getf HF (SPUle (kbytes vKn) (SLit hiA)) H1. getf HF (SPUle vDn (SLit hiA)) H2. getf HF (SPUle vE (SLit 4096)) H3.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi slot_obj].
  exact (PV.slot_range_eqs rho vDn vKn Ha Hb ltac:(ule47 H1) ltac:(ule47 H2) ltac:(ule_from H3)).
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
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
     smatch segsU rhoL L (tr', mkCfg ms' md') ->
     JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc P0_vr FBc tv0) Pre_vr rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => P0_vr) PD_vr FBc)).
Hypothesis REENTER : forall T tv rT vT rho b,
  In (T, tv, (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc P0_vr FB tv) (Posts_vp Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let CLIENT := client_callT segsU C_U NF Kc rho0 P0_vr FB ML (fun _ => P0_vr) Pre_vr tv0 PD_vr NF
  (@eq_refl positive (ss_next Pre_vr)) TR TR_facts TR_ex TR_pre TR_callP CVR.

Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia].

Lemma X_P_fail : forall rho b, TR (SPJ segsU (JGv tv0) P_push_fail rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_keep : forall rho b, TR (SPJ segsU (JGv tv0) P_push_keep rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.
Lemma X_P_grown : forall rho b, TR (SPJ segsU (JGv tv_post) P_push_grown rho) (FAM b).
Proof. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_vr : forall rho, TR (SPJ segsU (JGv tv0) E_vr0 rho) (FAM (emeas (E_vr0, tv0, (90, z0)) rho)).
Proof.
  intros rho.
  eapply TR_pre.
  2: { change (JGv tv0) with (JGv ([] ++ tv0)).
       apply (CLIENT E_vr s_vr R_vr rho [] tv0 _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav _ _ _ _ _ HT. split.
         + eapply robjs_checkF_sound with (extra := fun _ => false);
             [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | constructor
             | vm_compute; reflexivity | intros o a _ X; discriminate X].
         + cbn beta. pose proof (P0_vr_at rho Hav HP0) as HP1.
           unfold P0_vr in HP1 |- *. rewrite !rw_call'. change (wsub_get s_vr 15) with vD. change (wsub_get s_vr 17) with vK.
           unfold vD, vK. rewrite !eval_var. exact HP1.
       - intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + replace (T_after E_vr s_vr R_vr P_keep) with T_keep0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_keep (ss_next E_vr)) tv0) with tv0 by (vm_compute; reflexivity).
           eapply TR_pre; [intros w Hw; exact (keepC_ok rho' w Hw) | reenter T_keepC tv0 80].
         + replace (T_after E_vr s_vr R_vr P_fail) with T_fail0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_fail (ss_next E_vr)) tv0) with tv0 by (vm_compute; reflexivity).
           reenter T_fail0 tv0 80.
         + replace (T_after E_vr s_vr R_vr P_grown) with T_grown0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF P_grown (ss_next E_vr)) tv_post) with tv_post by (vm_compute; reflexivity).
           eapply TR_pre; [intros w Hw; exact (grownC_ok rho' w Hw) | reenter T_grownC tv_post 80]. }
  intros w Hw. apply (SPJ_unbase segsU _ rho E_vr1 1 (-32) E_vr w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_vr rho E_vr0 E_vr1 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma X_fail_ok : forall rho b, TR (SPJ segsU (JGv tv0) X_fail rho) (FAM b).
Proof.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0) P_push_fail r w)); [ | apply TR_exw; intros r; apply X_P_fail ].
  intros w Hw. exists (rho_sub rho s_xf).
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML X_fail3 P_push_fail s_xf tv0 tv0 rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segsU _ rho X_fail2 0 (-16) X_fail3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_f rho X_fail X_fail2 w ltac:(vm_compute; reflexivity)). exact Hw.
Qed.

Lemma X_keep_ok : forall rho b, TR (SPJ segsU (JGv tv0) X_keep rho) (FAM b).
Proof.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv0) P_push_keep r w)); [ | apply TR_exw; intros r; apply X_P_keep ].
  intros w Hw. exists (rho_sub rho s_xk).
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML X_keep3 P_push_keep s_xk tv0 tv0 rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segsU _ rho X_keep2 0 (-16) X_keep3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_k rho X_keep1 X_keep2 w ltac:(vm_compute; reflexivity)).
  unfold X_keep1. eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
  intros HF.
  getf HF (SPUle (kbytes vC) (kbytes vK)) Ha. getf HF (SPUle (SAlu ALU_ADD (kbytes vC) vE) (kbytes vK)) Hb.
  getf HF (SPUle (kbytes vK) (SLit two47)) H1. getf HF (SPUle vD (SLit two47)) H2. getf HF (SPUle vE (SLit 4096)) H3.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi mid_obj].
  destruct (PV.slot_range_eqs rho vD vK Ha Hb ltac:(ule_from H1) ltac:(ule_from H2) ltac:(ule_from H3)) as [E1 E2].
  split; [symmetry; exact E1 | symmetry; exact E2].
Qed.

Lemma X_grown_ok : forall rho b, TR (SPJ segsU (JGv tv_post) X_grown rho) (FAM b).
Proof.
  intros rho b.
  apply (TR_pre (fun w => exists r, SPJ segsU (JGv tv_post) P_push_grown r w)); [ | apply TR_exw; intros r; apply X_P_grown ].
  intros w Hw. exists (rho_sub rho s_xg).
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 P0_vr FB ML X_grown3 P_push_grown s_xg tv_post tv_post rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
  apply (SPJ_unbase segsU _ rho X_grown2 0 (-16) X_grown3 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_xforms segsU _ xs_g rho X_grown1 X_grown2 w ltac:(vm_compute; reflexivity)).
  unfold X_grown1. eapply SPJ_reshape; [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
  intros HF.
  getf HF (SPUle (kbytes vC) (kbytes vKn)) Ha. getf HF (SPUle (SAlu ALU_ADD (kbytes vC) vE) (kbytes vKn)) Hb.
  getf HF (SPUle (kbytes vKn) (SLit hiA)) H1. getf HF (SPUle vDn (SLit hiA)) H2. getf HF (SPUle vE (SLit 4096)) H3.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi mid_obj].
  destruct (PV.slot_range_eqs rho vDn vKn Ha Hb ltac:(ule47 H1) ltac:(ule47 H2) ltac:(ule_from H3)) as [E1 E2].
  split; [symmetry; exact E1 | symmetry; exact E2].
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_vr.
  - apply X_fail_ok.
  - apply X_keep_ok.
  - apply X_grown_ok.
Qed.
End SumT.

Theorem vp_sum_S : triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vp rho0) Q.
Proof using HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 P0_vr FB ML FUEL_vp cutpcs_vp 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (call_soundP segsU ok)).
       - intros FBc rho1. exact (vr.vr_sum ok Kc FBc rho1 HS ML MC).
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segsU C_U NF Kc rho0 P0_vr FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc P0_vr FB ok rho0 tv (Posts_vp Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.

Theorem vp_sum_E : etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vp rho0) Q.
Proof using Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 P0_vr FB ML FUEL_vp cutpcs_vp 100 cutsE exitsE Q ejcert_ok)
         with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 P0_vr FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (call_completeP segsU)).
       - intros FBc rho1. exact (vr.vr_sum_ex Kc FBc rho1 Hvi ML MCX).
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segsU C_U NF Kc rho0 P0_vr FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc P0_vr FB rho0 tv (Posts_vp Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem vp_sum : vp_stmt_U.
Proof. intros ok Kc FB rho0 HS ML MC. apply vp_sum_S; assumption. Qed.

Theorem vp_sum_ex : vp_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi ML MCX. apply vp_sum_E; assumption. Qed.
