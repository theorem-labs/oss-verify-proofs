From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_bli.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require S_vrd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11.S_vrd.

Definition bli_LI : Z := 0x15180.
Definition ra_vr : Z := 0x151b4.
Definition bli_trap : Z := 0x152c8.
Definition FUEL_bli : nat := 500%nat.
Definition cutpcs_bli : list Z := [VRD.vr_entry; bli_LI].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_bli cutpcs_bli S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_bli end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition bli_xregs : list sv := map (fun r => if callee_saved r then pre_reg r else hx r) (seq 0 32).
Definition HNEXT : positive := 300.
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282.
Definition pI : sv := SVar 283. Definition pJ : sv := SVar 284.
Definition notBUF : sv := SAlu ALU_XOR vBUF (SLit 18446744073709551615).

Definition F_saved : list cell :=
  [c8 (-88) (SVar 45); c8 (-80) (SVar 44); c8 (-72) (SVar 43); c8 (-64) (SVar 42); c8 (-56) (SVar 41);
   c8 (-48) (SVar 40); c8 (-40) (SVar 39); c8 (-32) (SVar 38); c8 (-24) (SVar 29); c8 (-16) (SVar 28);
   c8 (-8) (SVar 11)].

Definition body_regs (l : list (nat * sv)) : list sv :=
  setregs bli_xregs ([(1%nat, hx 1); (2%nat, spo (- FR)); (8%nat, vLEN); (9%nat, vBUF); (18%nat, vAL); (19%nat, vV);
                      (20%nat, SLit 1); (21%nat, notBUF); (22%nat, pI); (23%nat, SLit 10); (24%nat, SLit 13);
                      (25%nat, pJ)] ++ l).

Definition HSd (pc : Z) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate :=
  mkSS pc (body_regs regs) pre_fregs FcsrFrm0 None (objs_of_darr F_saved d c k)
    (facts ++ vec_facts d c k dv ++ bli_facts) HNEXT false.

Definition ij_facts : list sprop := [SPUle pI pJ; SPUle pI (SLit (2 ^ 26)); SPUle pJ (SLit (2 ^ 26))].
Definition darr_inv : list sprop := [SPUle pC pI; SPBranch BC_LTU pI vLEN].

Definition C_LId : sstate :=
  HSd bli_LI [] pD pC pK 280 ([SPBranch BC_LTU pJ vLEN] ++ ij_facts ++ darr_inv).
Definition E_vrd : sstate :=
  HSd VRD.vr_entry [(1%nat, SLit ra_vr); (10%nat, vV); (11%nat, SAlu ALU_ADD pC (SLit 1)); (12%nat, vAL)]
    pD pC pK 280 ([SPUle pJ vLEN] ++ ij_facts ++ darr_inv).
Definition K_okd : sstate :=
  HSd VRD.vr_ret [(1%nat, SLit ra_vr); (10%nat, SLit 1)] pD pC pK 280
    ([SPUle (SAlu ALU_ADD pC (SLit 1)) pK; SPUle pJ vLEN] ++ ij_facts ++ darr_inv).
Definition K_faild : sstate :=
  HSd VRD.vr_ret [(1%nat, SLit ra_vr); (10%nat, SLit 0)] pD pC pK 280
    ([SPUle pJ vLEN] ++ ij_facts ++ darr_inv).

Definition tvB : list (sv * sv) := [(pD, kb16 pK)].

Definition E_vr1d : sstate := Eval vm_compute in optS (apply_xforms E_vrd [XSplit 1 (SLit (-32))]).
Definition E_vr2d : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1d 1 (-32)).
Definition s_vrd : wsub :=
  [(19%positive, SAlu ALU_ADD vDp (SLit 32)); (15%positive, pD); (16%positive, pC); (17%positive, pK);
   (52%positive, vLEN)] ++ infer_sub 10 E_vr2d VRD.Pre_vr.
Definition R_vrd : list sobj := Eval vm_compute in optR (entails_fr E_vr2d VRD.Pre_vr s_vrd).
Definition PD_vrd : list pdesc := VRD.PD_vr.

Definition xs_keep : list xform := [XRebase 0; XRebase 1; XSelect [1; 0; 2; 3; 4; 5; 6]%nat; XMerge 0].
Definition xs_grown : list xform := [XRebase 0; XRebase 2; XSelect [0; 2; 1; 3; 4; 5; 6]%nat; XMerge 0].

Definition VL (j : sv) (ph : Z) : sv :=
  SAlu ALU_ADD (SMd M_MUL (SLit 8) (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 26 + 16)) vLEN) j)) (SLit ph).
Definition z0 : sv := SLit 0.

Definition cutsEd : list edesc :=
  [((Pre_bli0, tv0), (100, z0)); ((C_LId, tvB), (50, VL pJ 5)); ((K_okd, tvB), (50, VL pJ 3));
   ((K_faild, tvB), (45, z0))].

Definition X_nulld : sstate := Eval vm_compute in nth 0 (leaves_at K_okd bli_trap) Pre_bli.
Definition X_nulld2 : sstate := Eval vm_compute in nth 1 (leaves_at K_okd bli_trap) Pre_bli.
Definition exitsEd : list edesc :=
  [((E_vrd, tvB), (50, VL pJ 4)); ((P_ret_darr, tvP), (0, z0)); ((X_nulld, tvB), (0, z0));
   ((X_nulld2, tvB), (0, z0))].

Definition is_txt (o : sobj) : bool :=
  sv_eqb (ob_base o) vBUF && sv_eqb (ob_lo o) (SLit 0) && sv_eqb (ob_hi o) vLEN.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF eq_refl) end.

Lemma call_check_vrd :
  call_checkP E_vr2d VRD.Pre_vr s_vrd R_vrd [VRD.P_keep; VRD.P_fail; VRD.P_grown] = true /\ length R_vrd = 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition xn_a1 : sv := SAlu ALU_SLTU (SLit 0) pD.
Definition xn_a2 : sv := SAlu ALU_SLTU (SAlu ALU_ADD pD (SMd M_MUL (SLit 16) pC)) (SLit 1).
Definition xnull_a : sv := SAlu ALU_XOR xn_a1 xn_a2.
Definition Fx_nulld : list sprop := SPNot (SPBranch BC_EQ pD (SLit 0)) :: tl (ss_facts X_nulld).

Lemma xn_a1_decided : decide_t (mk_ctx Fx_nulld) BC_EQ xn_a1 (SLit 1) = DTrue.
Proof. vm_compute. reflexivity. Qed.
Lemma xn_a2_decided : decide_t (mk_ctx Fx_nulld) BC_EQ xn_a2 (SLit 0) = DTrue.
Proof. vm_compute. reflexivity. Qed.

Lemma bt_eq_lit : forall r a z, branch_taken BC_EQ (eval r a) (eval r (SLit z)) = true -> eval r a = eval r (SLit z).
Proof. intros r a z H. apply bv_eq. cbn [branch_taken] in H. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma Forall_tl_ok {A} (P : A -> Prop) (l : list A) : Forall P l -> Forall P (tl l).
Proof. destruct 1; [constructor | assumption]. Qed.

Lemma null_zero_contra : forall r, holds r (SPBranch BC_EQ pD (SLit 0)) ->
  holds r (SPUle (SAlu ALU_ADD pC (SLit 1)) pK) -> holds r (SPUle pK (SLit two47)) ->
  holds r (SPUle pC pI) -> holds r (SPUle pI (SLit (2 ^ 26))) ->
  (bv_unsigned (eval r pD) = 0 -> bv_unsigned (eval r (kb16 pK)) = 0) -> False.
Proof.
  intros r H0 H1 H2 H3 H4 Hz.
  unfold kb16, pK, pC, pD, pI, two47, S_vr.two47 in *. zfacts. nia.
Qed.

Ltac bound_facts HF :=
  have_fact HF (SPUle (SAlu ALU_ADD pC (SLit 1)) pK); rename H into H1;
  have_fact HF (SPUle pK (SLit two47)); rename H into H2;
  have_fact HF (SPUle pC pI); rename H into H3;
  have_fact HF (SPUle pI (SLit (2 ^ 26))); rename H into H4.

Lemma nulld_contra : forall r, Forall (holds r) (ss_facts X_nulld) ->
  (bv_unsigned (eval r pD) = 0 -> bv_unsigned (eval r (kb16 pK)) = 0) -> False.
Proof.
  intros r HF Hz. bound_facts HF.
  destruct (branch_taken BC_EQ (eval r pD) (eval r (SLit 0))) eqn:EB.
  - exact (null_zero_contra r EB H1 H2 H3 H4 Hz).
  - assert (HN0 : holds r (SPNot (SPBranch BC_EQ pD (SLit 0)))) by (cbn [holds]; rewrite EB; discriminate).
    pose proof (Forall_pick _ _ 0 (SPBranch BC_EQ xnull_a (SLit 0)) HF eq_refl) as Hx.
    pose proof (mk_ctx_ok r Fx_nulld ltac:(constructor; [exact HN0 | exact (Forall_tl_ok _ _ HF)])) as Hdg.
    pose proof (decide_t_sound r _ BC_EQ xn_a1 (SLit 1) Hdg) as D1. rewrite xn_a1_decided in D1.
    pose proof (decide_t_sound r _ BC_EQ xn_a2 (SLit 0) Hdg) as D2. rewrite xn_a2_decided in D2.
    apply bt_eq_lit in D1. apply bt_eq_lit in D2.
    cbn [holds] in Hx. change (eval r xnull_a) with (alu64 ALU_XOR (eval r xn_a1) (eval r xn_a2)) in Hx.
    rewrite D1, D2 in Hx. vm_compute in Hx. discriminate.
Qed.

Lemma nulld2_contra : forall r, Forall (holds r) (ss_facts X_nulld2) ->
  (bv_unsigned (eval r pD) = 0 -> bv_unsigned (eval r (kb16 pK)) = 0) -> False.
Proof.
  intros r HF Hz. bound_facts HF.
  have_fact HF (SPBranch BC_EQ pD (SLit 0)). rename H into H0.
  exact (null_zero_contra r H0 H1 H2 H3 H4 Hz).
Qed.

Section Sum.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let nI : sstate * list (sv * sv) -> jnode := nodeI segsU C_U NF Kc rho0 (P0_bli FB) FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 (P0_bli FB) FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_bli_darr Kc FB).

Lemma ejcert_ok : ejcert segsU NF FUEL_bli cutpcs_bli 100 cutsEd exitsEd = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_extra_ok : forall rho kept R o a,
  P0_bli FB rho0 -> agree_vals NF rho0 rho -> In o R -> is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof using .
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold vBUF, vLEN in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 12%positive ltac:(reflexivity)), <- (Hw 13%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 13)) as R13.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 13))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho Q', (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') ->
  TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall P P' Q', (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) P Q', (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_contra : forall J X Q', (forall rho tr md, J rho tr md -> Forall (holds rho) (ss_facts X) -> False) ->
  forall rho, TR (SPJ segsU J X rho) Q'.
Hypothesis TR_callP : forall J Jp C Pre s R Posts Q' rho,
  SymEntail.entails_fr C Pre s = Some R ->
  call_checkP C Pre s R (map fst Posts) = true ->
  (forall rho1, TR (SPJ segsU Jp Pre rho1) (LQP segsU (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C (tr, Run.mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L JL tr ms md rhoL tr' ms' md', In (L, JL) Posts ->
     smatch segsU rho C (tr, Run.mkCfg ms md) -> J rho tr md ->
     agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) s) rhoL ->
     smatch segsU rhoL L (tr', Run.mkCfg ms' md') -> JL (rho_sub (rho_absorb rho R ms) s) rhoL tr' md' ->
     import_okP rho ms R s Pre L rhoL /\
     (forall rho', call_linkP rho ms R s Pre C L rho' rhoL ->
        TR (SPJ segsU (J_ofP JL (rho_sub (rho_absorb rho R ms) s) rhoL) (import_post s (ss_next Pre) L (ss_next C) R) rho') Q')) ->
  TR (SPJ segsU J C rho) Q'.
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRD.P0_vr FBc VRD.tv0) VRD.Pre_vr rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => VRD.P0_vr) PD_vrd FBc)).
Hypothesis REENTER : forall T tv rv rho b, In ((T, tv), rv) cutsEd ->
  0 <= emeas ((T, tv), rv) rho < b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_bli FB) FB tv) (Posts_bli_darr Kc FB) ->
  TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let CLIENT := client_callT segsU C_U NF Kc rho0 (P0_bli FB) FB ML (fun _ => VRD.P0_vr) VRD.Pre_vr VRD.tv0 PD_vrd NF
  (@eq_refl positive (ss_next VRD.Pre_vr)) TR TR_facts TR_ex TR_pre TR_callP CVR.
Let CONT := contE_TR segsU C_U NF Kc rho0 (P0_bli FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma X_P_ret : forall rho b, TR (SPJ segsU (JGv tvP) P_ret_darr rho) (FAM b).
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_nulld_ok : forall rho b, TR (SPJ segsU (JGv tvB) X_nulld rho) (FAM b).
Proof using FB Kc TR_contra rho0.
  intros rho b. apply TR_contra. intros r tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HF.
  apply (nulld_contra r HF). intros HD0.
  apply (proj1 (Forall_forall _ _) HZ (pD, kb16 pK) ltac:(left; reflexivity)).
  intros Hnz. apply Hnz. exact HD0.
Qed.

Lemma X_nulld2_ok : forall rho b, TR (SPJ segsU (JGv tvB) X_nulld2 rho) (FAM b).
Proof using FB Kc TR_contra rho0.
  intros rho b. apply TR_contra. intros r tr md (Ai & Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HF.
  apply (nulld2_contra r HF). intros HD0.
  apply (proj1 (Forall_forall _ _) HZ (pD, kb16 pK) ltac:(left; reflexivity)).
  intros Hnz. apply Hnz. exact HD0.
Qed.

Lemma X_E_vr : forall rho, TR (SPJ segsU (JGv tvB) E_vrd rho) (FAM (emeas ((E_vrd, tvB), (50, VL pJ 4)) rho)).
Proof using CLIENT CONT REENTER nI.
  intros rho; eapply TR_pre.
  2: { change (JGv tvB) with (JGv ([] ++ tvB)).
       apply (CLIENT E_vr2d s_vrd R_vrd rho [] tvB _).
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute; reflexivity.
       - vm_compute; reflexivity.
       - intros Ai ms HF HP0 Hav X3 X4 X5 HZ X6 HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt).
           * exact HF. * exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT). * constructor. * vm_compute; reflexivity.
           * intros o a Ho Hx Hr; eapply txt_extra_ok; eauto.
         + cbn beta. unfold VRD.P0_vr.
           change (S_vr.P0_vr ?x) with (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.P0_vr x).
           eapply (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.P0_vr_of_tvz _ 280 282 16);
             [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF); vm_compute; tauto.
       - intros d rho' Hd Hag; destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2d) _ K_okd _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_okd tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_keep 0 (- FR) (ss_next E_vr2d) _ K_faild _ tvB tvB z0 45 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_faild tvB (45, z0) rho''); [apply (nth_error_In _ 3); reflexivity | rewrite emeas_emeasZ; exact Hm].
         + eapply (CONT xs_grown 0 (- FR) (ss_next E_vr2d) _ K_okd _ tvB tvB (VL pJ 3) 50 50 (VL pJ 4) rho rho').
           * vm_compute; reflexivity. * apply Permutation_refl. * exact Hag.
           * intros rho'' Hm. apply (REENTER K_okd tvB (50, VL pJ 3) rho''); [apply (nth_error_In _ 2); reflexivity | rewrite emeas_emeasZ; exact Hm]. }
  intros w Hw.
  apply (SPJ_unbase segsU _ rho E_vr1d 1 (-32) E_vr2d w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ [XSplit 1 (SLit (-32))] rho E_vrd E_vr1d w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : forall X tvX rvX rho, In ((X, tvX), rvX) exitsEd ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas ((X, tvX), rvX) rho)).
Proof using CLIENT CONT POST REENTER TR_contra nI.
  intros X tvX rvX rho Hin. cbn [exitsEd In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_vr.
  - apply X_P_ret.
  - apply X_nulld_ok.
  - apply X_nulld2_ok.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis VR : VRD.vr_darr_stmt_U.

Theorem build_line_index_darr_sum_U :
  triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_bli FB) FB tv0) Pre_bli0 rho0) (LQP segsU NF rho0 (Posts_bli_darr Kc FB)).
Proof using HS MC ML VR.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsEd exitsEd ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsEd)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @triple_ex segsU ok A P Q' H)
                (triple_pureh segsU ok) (triple_contraJ segsU ok)
                (call_soundP segsU ok)).
       - intros FBc rho1. exact (VR ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segsU C_U NF Kc rho0 (P0_bli FB) FB ok cutsEd T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc (P0_bli FB) FB ok rho0 tv (Posts_bli_darr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis VRX : VRD.vr_darr_ex_stmt_U.

Theorem build_line_index_darr_sum_ex_U :
  etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_bli FB) FB tv0) Pre_bli0 rho0) (LQP segsU NF rho0 (Posts_bli_darr Kc FB)).
Proof using Hvi MCX ML VRX.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 (P0_bli FB) FB ML FUEL_bli cutpcs_bli 100 cutsEd exitsEd Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 (P0_bli FB) FB) cutsEd) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun A P Q' H => @etriple_ex segsU A P Q' H)
                (etriple_pureh segsU) (etriple_contraJ segsU)
                (call_completeP segsU)).
       - intros FBc rho1. exact (VRX Kc FBc rho1 Hvi ML MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segsU C_U NF Kc rho0 (P0_bli FB) FB cutsEd T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc (P0_bli FB) FB rho0 tv (Posts_bli_darr Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem bli_darr_ok_U : VRD.vr_darr_stmt_U -> bli_darr_stmt_U.
Proof. intros VR ok Kc FB rho0 HS ML MC. exact (build_line_index_darr_sum_U Kc FB rho0 ML ok HS MC VR). Qed.
Theorem bli_darr_ex_ok_U : VRD.vr_darr_ex_stmt_U -> bli_darr_ex_stmt_U.
Proof. intros VRX Kc FB rho0 ML Hvi MCX. exact (build_line_index_darr_sum_ex_U Kc FB rho0 ML Hvi MCX VRX). Qed.
