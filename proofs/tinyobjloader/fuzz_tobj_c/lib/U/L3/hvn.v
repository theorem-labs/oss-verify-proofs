From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require Import S_hvn.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require Import S_sd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HandleVnAddrU ScanDoubleAddrU.

Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.
Module SDP := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.

Definition FUEL_hvn : nat := 400%nat.
Definition cutpcs_hvn : list Z := [sdU_entry; VRU.vr_entry].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_hvn cutpcs_hvn S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_hvn_U end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition objs_sd_U (cur : sv) : list sobj :=
  [HV.O_stk16; HV.O_c0 cur; HV.O_text; HV.O_out []; HV.O_Ftop HV.F_saved; HV.O_Dlow; HV.P_alloc;
   HV.P_st HV.vERR; HV.V184 HV.vND HV.vNC HV.vNK; O_al_U; HV.O_c8; HV.O_dat HV.vND HV.vNK].
Definition HS_U (pc : Z) (regs : list (nat * sv)) (cur : sv) (facts : list sprop) : sstate :=
  mkSS pc (HV.body_regs regs) HV.hvn_fregs FcsrFrm0 None (objs_sd_U cur) (facts ++ hvn_facts_U) HV.HNEXT false.

Definition E_A : sstate := Eval vm_compute in nth 0 (leaves_at Pre_hvn_U sdU_entry) Pre_hvn_U.
Definition E_A2 : sstate := Eval vm_compute in optS (apply_xforms E_A [XSplit 0 (SLit (-40)); XSplit 2 (SLit (-16))]).
Definition s_A : wsub := infer_sub 10 E_A2 Pre_sd_U.
Definition R_A : list sobj := Eval vm_compute in optR (entails_fr E_A2 Pre_sd_U s_A).
Definition TA (L : sstate) : sstate := T_after E_A2 s_A R_A L.
Definition T_A0 : sstate := Eval vm_compute in TA P_none_U.
Definition T_A1 : sstate := Eval vm_compute in TA (P_num_U sdU_ret_nan).
Definition T_A2 : sstate := Eval vm_compute in TA (P_num_U sdU_ret_num).
Definition T_A3 : sstate := Eval vm_compute in TA (P_num_U sdU_ret_inf).

Definition ra_B : Z := 0x19198.
Definition ra_C : Z := 0x191ac.
Definition ra_D : Z := 0x191d8.
Definition ra_E : Z := 0x191f8.
Definition ra_vr : Z := 0x1922c.

Definition E_sd_U (ra : Z) : sstate :=
  HS_U sdU_entry [(1%nat, SLit ra); (10%nat, HV.vc); (11%nat, SDP.pB SDP.vE); (12%nat, HV.spo (-48))] HV.pCUR HV.cur_facts.
Definition E_B : sstate := E_sd_U ra_B.
Definition E_C : sstate := E_sd_U ra_C.
Definition E_D : sstate := E_sd_U ra_D.
Definition E_E : sstate := E_sd_U ra_E.

Definition s_sd (E : sstate) : wsub := infer_sub 10 E Pre_sd_U.
Definition R_sd (E : sstate) : list sobj := optR (entails_fr E Pre_sd_U (s_sd E)).
Definition T_of (E : sstate) (L : sstate) : sstate := T_after E (s_sd E) (R_sd E) L.
Definition T_B0 : sstate := Eval vm_compute in T_of E_B P_none_U.
Definition T_B1 : sstate := Eval vm_compute in T_of E_B (P_num_U sdU_ret_nan).
Definition T_B2 : sstate := Eval vm_compute in T_of E_B (P_num_U sdU_ret_num).
Definition T_B3 : sstate := Eval vm_compute in T_of E_B (P_num_U sdU_ret_inf).
Definition T_C0 : sstate := Eval vm_compute in T_of E_C P_none_U.
Definition T_C1 : sstate := Eval vm_compute in T_of E_C (P_num_U sdU_ret_nan).
Definition T_C2 : sstate := Eval vm_compute in T_of E_C (P_num_U sdU_ret_num).
Definition T_C3 : sstate := Eval vm_compute in T_of E_C (P_num_U sdU_ret_inf).
Definition T_D0 : sstate := Eval vm_compute in T_of E_D P_none_U.
Definition T_D1 : sstate := Eval vm_compute in T_of E_D (P_num_U sdU_ret_nan).
Definition T_D2 : sstate := Eval vm_compute in T_of E_D (P_num_U sdU_ret_num).
Definition T_D3 : sstate := Eval vm_compute in T_of E_D (P_num_U sdU_ret_inf).
Definition T_E0 : sstate := Eval vm_compute in T_of E_E P_none_U.
Definition T_E1 : sstate := Eval vm_compute in T_of E_E (P_num_U sdU_ret_nan).
Definition T_E2 : sstate := Eval vm_compute in T_of E_E (P_num_U sdU_ret_num).
Definition T_E3 : sstate := Eval vm_compute in T_of E_E (P_num_U sdU_ret_inf).

Definition E_vr0 : sstate :=
  HS_U VRU.vr_entry [(1%nat, SLit ra_vr); (10%nat, SAlu ALU_ADD HV.vb (SLit 184));
                     (11%nat, SAlu ALU_ADD HV.vNC (SLit 3)); (12%nat, HV.vAL)] HV.pCUR HV.cur_facts.
Definition xs_vr : list xform := [XSplit 5 (SLit (-32)); XSelect [6; 0; 5; 1; 2; 3; 4; 7; 8; 9; 10; 11; 12]%nat; XMerge 0].
Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr0 xs_vr).
Definition E_vr : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-32)).
Definition s_vr : wsub :=
  [(19%positive, SAlu ALU_ADD HV.vDp (SLit 32)); (15%positive, HV.vND); (16%positive, HV.vNC);
   (17%positive, HV.vNK); (18%positive, SLit 4)] ++ infer_sub 10 E_vr VRU.Pre_vr.
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr VRU.Pre_vr s_vr).
Definition T_keep0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr VRU.P_keep.
Definition T_fail0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr VRU.P_fail.
Definition T_grown0 : sstate := Eval vm_compute in T_after E_vr s_vr R_vr VRU.P_grown.

Definition nz_keep : list (positive * Z * positive) := [(54%positive, 4, 56%positive)].
Definition T_keep1 : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_keep) T_keep0.

Definition X_keep3 : sstate := Eval vm_compute in nth 0 (leaves_at T_keep1 hvnU_ret3) Pre_hvn_U.
Definition X_grown3 : sstate := Eval vm_compute in nth 0 (leaves_at T_grown0 hvnU_ret3) Pre_hvn_U.
Definition X_Fv1 : sstate := Eval vm_compute in nth 0 (leaves_at T_fail0 hvnU_ret1) Pre_hvn_U.
Definition X_Fv2 : sstate := Eval vm_compute in nth 0 (leaves_at T_fail0 hvnU_ret2) Pre_hvn_U.

Definition X_keep3b : sstate := Eval vm_compute in optS (apply_xforms X_keep3 HV.xs_keep).
Definition X_keep3c : sstate := Eval vm_compute in optS (unbase_obj_at X_keep3b 1 (-48)).
Definition X_grown3b : sstate := Eval vm_compute in optS (apply_xforms X_grown3 HV.xs_grown).
Definition X_grown3c : sstate := Eval vm_compute in optS (unbase_obj_at X_grown3b 1 (-48)).
Definition X_Fv1b : sstate := Eval vm_compute in optS (apply_xforms X_Fv1 HV.xs_keep).
Definition X_Fv1c : sstate := Eval vm_compute in optS (unbase_obj_at X_Fv1b 1 (-48)).
Definition X_Fv2b : sstate := Eval vm_compute in optS (apply_xforms X_Fv2 HV.xs_keep).
Definition X_Fv2c : sstate := Eval vm_compute in optS (unbase_obj_at X_Fv2b 1 (-48)).

Definition s_post (X : sstate) (pc : Z) : wsub := infer_sub 100 X (P_ret_U pc).

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : forall n : sstate * list (sv * sv), jnode := nodeI segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB tv.
Let Q : assn := LQP segsU NF rho0 (Posts_hvn_U Kc FB).

Definition z0 : sv := SLit 0.
Definition cutsE : list edesc :=
  [(Pre_hvn_U, HV.tv0, (100, z0));
   (T_A0, HV.tv0, (90, z0)); (T_A1, HV.tv0, (90, z0)); (T_A2, HV.tv0, (90, z0)); (T_A3, HV.tv0, (90, z0));
   (T_B0, HV.tv0, (80, z0)); (T_B1, HV.tv0, (80, z0)); (T_B2, HV.tv0, (80, z0)); (T_B3, HV.tv0, (80, z0));
   (T_D0, HV.tv0, (80, z0)); (T_D1, HV.tv0, (80, z0)); (T_D2, HV.tv0, (80, z0)); (T_D3, HV.tv0, (80, z0));
   (T_C0, HV.tv0, (70, z0)); (T_C1, HV.tv0, (70, z0)); (T_C2, HV.tv0, (70, z0)); (T_C3, HV.tv0, (70, z0));
   (T_E0, HV.tv0, (70, z0)); (T_E1, HV.tv0, (70, z0)); (T_E2, HV.tv0, (70, z0)); (T_E3, HV.tv0, (70, z0));
   (T_keep1, HV.tv0, (50, z0)); (T_grown0, HV.tvG, (50, z0)); (T_fail0, HV.tv0, (50, z0))].
Definition exitsE : list edesc :=
  [(E_A, HV.tv0, (95, z0)); (E_B, HV.tv0, (85, z0)); (E_D, HV.tv0, (85, z0)); (E_C, HV.tv0, (75, z0));
   (E_E, HV.tv0, (75, z0)); (E_vr0, HV.tv0, (55, z0));
   (X_keep3, HV.tv0, (10, z0)); (X_grown3, HV.tvG, (10, z0)); (X_Fv1, HV.tv0, (10, z0)); (X_Fv2, HV.tv0, (10, z0))].
Lemma ejcert_ok : ejcert segsU NF FUEL_hvn cutpcs_hvn 100 cutsE exitsE = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_extra_ok_U : forall rho kept R o a,
  HV.P0_hvn FB rho0 -> agree_vals NF rho0 rho -> In o R -> HV.is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof using .
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold HV.is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold SDP.vB, SDP.vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 15%positive ltac:(reflexivity)), <- (Hw 18%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 18)) as R18.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 18))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML TR TR_facts TR_pre)).

Hypothesis CSD : forall tv rho rho1,
  TR (SP segsU (fun tr md => JGv tv rho tr md) Pre_sd_U rho1)
     (LQ segsU (fun tr md => JGv tv rho tr md) (ss_next Pre_sd_U) rho1 Posts_sd_U).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => VRU.P0_vr) VRU.PD_vr FBc)).
Hypothesis REENTER : forall T tv rT vT rho b,
  In (T, tv, (rT, vT)) cutsE -> 0 <= rT -> (rT + 1) * 2 ^ 64 <= b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc (HV.P0_hvn FB) FB tv) (Posts_hvn_U Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let PURE := pure_callT segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML TR TR_facts TR_pre TR_callJ.
Let CLIENT := client_callT segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre TR_callP CVR.

Lemma bound_ge : forall r b rho v,
  (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v) <-> r + 1 <= b \/ (r + 1) * 2 ^ 64 <= b * 2 ^ 64 + bv_unsigned (eval rho v).
Proof using . intros. pose proof (urange (eval rho v)). nia. Qed.
Ltac reenter T tv rT := apply (REENTER T tv rT z0); [cbn; tauto | lia | first [lia | unfold emeas, ed_rank, ed_var; cbn [fst snd]; apply bound_ge; left; lia]].

Lemma X_P_ret : forall pc rho b, In pc [hvnU_ret1; hvnU_ret2; hvnU_ret3] ->
  TR (SPJ segsU (JGv HV.tvP) (P_ret_U pc) rho) (FAM b).
Proof. intros pc rho b Hin. apply POST. destruct Hin as [<-|[<-|[<-|[]]]]; cbn; tauto. Qed.

Ltac sd_cont T rT :=
  match goal with |- TR (SPJ _ _ ?X _) _ => replace X with T by (vm_compute; reflexivity) end; reenter T HV.tv0 rT.
Ltac sd_site E T0 T1 T2 T3 rT :=
  apply (PURE E Pre_sd_U (s_sd E) (R_sd E) Posts_sd_U _ HV.tv0 _ (CSD HV.tv0 _));
  [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
  | intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
    [ sd_cont T0 rT | sd_cont T1 rT | sd_cont T2 rT | sd_cont T3 rT ] ].

Lemma X_E_A : forall rho b, 91 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_A rho) (FAM b).
Proof.
  intros rho b Hb. eapply TR_pre.
  2: { apply (PURE E_A2 Pre_sd_U s_A R_A Posts_sd_U rho HV.tv0 _ (CSD HV.tv0 rho));
       [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL _; destruct HinL as [<-|[<-|[<-|[<-|[]]]]]; cbn [lf_state];
         [ sd_cont T_A0 90 | sd_cont T_A1 90 | sd_cont T_A2 90 | sd_cont T_A3 90 ]. }
  intros w Hw. exact (SPJ_xforms segsU _ [XSplit 0 (SLit (-40)); XSplit 2 (SLit (-16))] rho E_A E_A2 w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_E_B : forall rho b, 81 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_B rho) (FAM b).
Proof. intros rho b Hb. sd_site E_B T_B0 T_B1 T_B2 T_B3 80. Qed.
Lemma X_E_D : forall rho b, 81 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_D rho) (FAM b).
Proof. intros rho b Hb. sd_site E_D T_D0 T_D1 T_D2 T_D3 80. Qed.
Lemma X_E_C : forall rho b, 71 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_C rho) (FAM b).
Proof. intros rho b Hb. sd_site E_C T_C0 T_C1 T_C2 T_C3 70. Qed.
Lemma X_E_E : forall rho b, 71 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_E rho) (FAM b).
Proof. intros rho b Hb. sd_site E_E T_E0 T_E1 T_E2 T_E3 70. Qed.

Lemma X_E_vr : forall rho b, 51 * 2 ^ 64 <= b -> TR (SPJ segsU (JGv HV.tv0) E_vr0 rho) (FAM b).
Proof.
  intros rho b Hb.
  eapply TR_pre.
  2: { change (JGv HV.tv0) with (JGv ([] ++ HV.tv0)).
       apply (CLIENT E_vr s_vr R_vr rho [] HV.tv0 _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
         + eapply robjs_checkF_sound with (extra := HV.is_txt); [exact HF | exact (TobjJVx.T_ok_T0_NF _ _ _ Hav HT) | constructor | vm_compute; reflexivity |].
           intros o a Ho Hx Hr. eapply txt_extra_ok_U; eauto.
         + cbn beta. eapply (HV.P0_vr_of_tvz rho 54 56 4); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
       - intros d rho' Hd _. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + replace (T_after E_vr s_vr R_vr VRU.P_keep) with T_keep0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_keep (ss_next E_vr)) VRU.tv0) with HV.tv0 by (vm_compute; reflexivity).
           apply (TR_pre (SPJ segsU (JGv HV.tv0) T_keep1 rho')); [| reenter T_keep1 HV.tv0 50].
           intros w Hw. replace T_keep1 with (add_facts (TobjJVx.nz_facts nz_keep) T_keep0) by (vm_compute; reflexivity).
           apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
           intros tr md HJ HFX.
           eapply (TobjJVx.nz_facts_sound segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB (ss_facts T_keep0) HV.tv0);
             [vm_compute; reflexivity | exact HFX | exact HJ].
         + replace (T_after E_vr s_vr R_vr VRU.P_fail) with T_fail0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_fail (ss_next E_vr)) VRU.tv0) with HV.tv0 by (vm_compute; reflexivity).
           reenter T_fail0 HV.tv0 50.
         + replace (T_after E_vr s_vr R_vr VRU.P_grown) with T_grown0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_grown (ss_next E_vr)) VRU.tv_post) with HV.tvG by (vm_compute; reflexivity).
           reenter T_grown0 HV.tvG 50. }
  intros w Hw.
  apply (SPJ_unbase segsU _ rho E_vr1 1 (-32) E_vr w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ xs_vr rho E_vr0 E_vr1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Ltac to_post X Xc pc tv :=
  intros rho b;
  apply (TR_pre (SPJ segsU (JGv HV.tvP) (P_ret_U pc) (rho_sub rho (s_post Xc pc)))); [ | apply X_P_ret; cbn; tauto ];
  intros w Hw;
  apply (SPJ_entails_JG segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML Xc (P_ret_U pc) _ tv HV.tvP rho w);
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
Lemma X_keep3_ok : forall rho b, TR (SPJ segsU (JGv HV.tv0) X_keep3 rho) (FAM b).
Proof.
  to_post X_keep3 X_keep3c hvnU_ret3 HV.tv0.
  apply (SPJ_unbase segsU _ rho X_keep3b 1 (-48) X_keep3c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ HV.xs_keep rho X_keep3 X_keep3b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_grown3_ok : forall rho b, TR (SPJ segsU (JGv HV.tvG) X_grown3 rho) (FAM b).
Proof.
  to_post X_grown3 X_grown3c hvnU_ret3 HV.tvG.
  apply (SPJ_unbase segsU _ rho X_grown3b 1 (-48) X_grown3c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ HV.xs_grown rho X_grown3 X_grown3b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_Fv1_ok : forall rho b, TR (SPJ segsU (JGv HV.tv0) X_Fv1 rho) (FAM b).
Proof.
  to_post X_Fv1 X_Fv1c hvnU_ret1 HV.tv0.
  apply (SPJ_unbase segsU _ rho X_Fv1b 1 (-48) X_Fv1c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ HV.xs_keep rho X_Fv1 X_Fv1b w ltac:(vm_compute; reflexivity) Hw).
Qed.
Lemma X_Fv2_ok : forall rho b, TR (SPJ segsU (JGv HV.tv0) X_Fv2 rho) (FAM b).
Proof.
  to_post X_Fv2 X_Fv2c hvnU_ret2 HV.tv0.
  apply (SPJ_unbase segsU _ rho X_Fv2b 1 (-48) X_Fv2c w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ HV.xs_keep rho X_Fv2 X_Fv2b w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; injection H as <- <- <-;
    unfold emeas, ed_rank, ed_var; cbn [fst snd]; try (pose proof (urange (eval rho z0))).
  - apply X_E_A. lia.
  - apply X_E_B. lia.
  - apply X_E_D. lia.
  - apply X_E_C. lia.
  - apply X_E_E. lia.
  - apply X_E_vr. lia.
  - apply X_keep3_ok.
  - apply X_grown3_ok.
  - apply X_Fv1_ok.
  - apply X_Fv2_ok.
Qed.
End SumT.

Section Safety.
Hypothesis SDS : scan_double_sum_stmt_U.
Hypothesis VRS : VRU.vr_stmt_U.

Theorem handle_vn_sum :
  triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (HV.P0_hvn FB) FB HV.tv0) Pre_hvn_U rho0) (LQP segsU NF rho0 (Posts_hvn_U Kc FB)).
Proof using HS MC ML SDS VRS.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML FUEL_hvn cutpcs_hvn 100 cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NF _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_soundP segsU ok) (call_soundJ segsU ok)).
       - intros tv rho rho1. apply SDS.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros FBc rho1. apply (VRS ok Kc FBc rho1 HS ML MC).
       - intros T tv rT vT rho b Hin _ _. exact (reenter_cutGE segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ok cutsE T tv (rT, vT) Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NF Kc (HV.P0_hvn FB) FB ok rho0 tv (Posts_hvn_U Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis SDX : scan_double_sum_ex_stmt_U.
Hypothesis VRX : VRU.vr_ex_stmt_U.

Theorem handle_vn_sum_ex :
  etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (HV.P0_hvn FB) FB HV.tv0) Pre_hvn_U rho0) (LQP segsU NF rho0 (Posts_hvn_U Kc FB)).
Proof using Hvi MCX ML SDX VRX.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB ML FUEL_hvn cutpcs_hvn 100 cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_completeP segsU) (call_completeJ segsU)).
       - intros tv rho rho1. apply SDX.
       - intros FBc rho1. apply (VRX Kc FBc rho1 Hvi ML MCX).
       - intros T tv rT vT rho b Hin H0 Hb. apply (ereenter_cutE segsU C_U NF Kc rho0 (HV.P0_hvn FB) FB cutsE T tv (rT, vT) Q b rho Hin).
         unfold emeas, ed_rank, ed_var. cbn [fst snd]. pose proof (urange (eval rho vT)). nia.
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NF Kc (HV.P0_hvn FB) FB rho0 tv (Posts_hvn_U Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem handle_vn_sum_U (SDS : scan_double_sum_stmt_U) (VRS : VRU.vr_stmt_U) : handle_vn_stmt_U.
Proof. intros ok Kc FB rho0 HS ML MC. exact (handle_vn_sum ok Kc FB rho0 HS ML MC SDS VRS). Qed.

Theorem handle_vn_sum_ex_U (SDX : scan_double_sum_ex_stmt_U) (VRX : VRU.vr_ex_stmt_U) : handle_vn_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi ML MCX. exact (handle_vn_sum_ex Kc FB rho0 ML Hvi MCX SDX VRX). Qed.
