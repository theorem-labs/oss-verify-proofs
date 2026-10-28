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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require Import S_hp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require S_pc.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_da S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LP := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs.
Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module DA := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_da.
Module VRU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_vr.

Definition z0 : sv := SLit 0.
Definition VTU (cv : sv) (ph : Z) : sv := SAlu ALU_ADD (SMd M_MUL (SLit 16) (SAlu ALU_SUB xE0 cv)) (SLit ph).

Definition lregsP_U : list (nat * sv) :=
  [(2%nat, spo (-112)); (8%nat, vc); (9%nat, vb); (18%nat, xb 688); (19%nat, SLit 66708);
   (20%nat, spo (-108)); (21%nat, SLit 32); (22%nat, SLit 9); (23%nat, SLit 1);
   (24%nat, SAlu ALU_SUB (SLit 0) (spo (-108))); (25%nat, SLit 12297829382473034411); (26%nat, SLit 2);
   (27%nat, SVar 47)].

Definition HPs_U (pc : Z) (regs : list (nat * sv)) (cur : sv) (pv : sv * sv * sv) (hp : sv) (facts : list sprop) : sstate :=
  mkSS pc (setregs hf_xregs (lregsP_U ++ regs)) hf_fregs FcsrFrm0 None
    ([O_F HP_U FP_saved_U; O_Dw HP_U] ++ LP.builderP pERR pv hp ++
     [O_al HP_U; O_c cur; O_text; LP.dd pv 12; O_ce])
    (facts ++ [SPUle hp (SLit 1)] ++ pvec_facts pv 12 ++ LP.lp_base_facts HP_U) HNEXT false.

Definition H60 : sstate := HPs_U 0x1a360 [] pP LP.pi1 pHP [SPUle xP0 pP; SPUle pP xE0].
Definition H70 : sstate := HPs_U 0x1a370 [(10%nat, txt pQ); (12%nat, txt xE0)] pP LP.pi1 pHP
  [SPUle xP0 pP; SPUle pP pQ; SPUlt pQ xE0].
Definition HB8 : sstate := HPs_U 0x1a3b8
  [(10%nat, txt pT0); (11%nat, txt pQ); (12%nat, txt xE0); (13%nat, SAlu ALU_ADD (txt pQ) (SLit 1))] pQ LP.pi1 pHP
  [SPUle xP0 pT0; SPUle pT0 pQ; SPUlt pQ xE0].

Definition E_pc_U : sstate := HPs_U PCU.ParseCornerAddrU.pcU_entry
  [(1%nat, SLit 0x1a424); (10%nat, txt pT0); (11%nat, pX); (12%nat, SVar 111); (13%nat, SAlu ALU_SRL (SVar 117) (SLit 1));
   (14%nat, SAlu ALU_SRL (SMd M_MULHU (SVar 114) (SLit 12297829382473034411)) (SLit 1)); (15%nat, spo (-108))]
  pC LP.pi1 pHP
  [SPUle xP0 pT0; SPUle pT0 pC; SPUle pC xE0;
   SPEq (SAlu ALU_ADD pT0 pX) pC; SPUle (SAlu ALU_ADD pT0 pX) xE0; SPUle pX (SLit 67108864)].
Definition E_vr_U : sstate := HPs_U VRU.vr_entry
  [(1%nat, SLit 0x1a45c); (10%nat, xb 688); (11%nat, SAlu ALU_ADD (t_c LP.pi1) (SLit 1)); (12%nat, xAL)]
  pC LP.pi1 pHP [SPUle xP0 pC; SPUle pC xE0].

Definition FUEL_hp : nat := 1000%nat.
Definition cutpcs_hp : list Z := [VRU.vr_entry; PCU.ParseCornerAddrU.pcU_entry; DA.da_entry; 0x1a360; 0x1a370; 0x1a3b8].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_hp cutpcs_hp S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_hp_U end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition xs_pc : list xform := [XSplit 0 (SLit (-108)); XSplit 1 (SLit (-96)); XSplit 3 (SLit (-64))].
Definition E_pc1 : sstate := Eval vm_compute in optS (apply_xforms E_pc_U xs_pc).
Definition E_pc2 : sstate := Eval vm_compute in optS (unbase_obj_at E_pc1 1 (-108)).
Definition s_pc : wsub := Eval vm_compute in infer_sub 10 E_pc2 PCU.Pre_pc_U.
Definition R_pc : list sobj := Eval vm_compute in optR (entails_fr E_pc2 PCU.Pre_pc_U s_pc).
Definition T_pc0 : sstate := Eval vm_compute in T_after E_pc2 s_pc R_pc PCU.P_ret_U.
Definition xs_pcm : list xform :=
  [XRebase 2; XSelect [3; 2; 4; 5; 0; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 1; 18; 19]%nat;
   XMerge 0; XMerge 0; XMerge 1].
Definition T_pc1 : sstate := Eval vm_compute in optS (apply_xforms T_pc0 xs_pcm).

Definition E_da : sstate := Eval vm_compute in nth 0 (leaves_at T_pc1 DA.da_entry) Pre_hp_U.
Definition xs_da : list xform := [XSplit 1 (SLit (-64))].
Definition E_da1 : sstate := Eval vm_compute in optS (apply_xforms E_da xs_da).
Definition s_da : wsub := Eval vm_compute in infer_sub 10 E_da1 DA.Pre_da.
Definition R_da : list sobj := Eval vm_compute in optR (entails_fr E_da1 DA.Pre_da s_da).
Definition T_da0 : sstate := Eval vm_compute in T_after E_da1 s_da R_da DA.P_da.
Definition xs_dam : list xform := [XSelect [1; 2; 0; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]%nat; XMerge 1].
Definition T_da1 : sstate := Eval vm_compute in optS (apply_xforms T_da0 xs_dam).

Definition xs_vr : list xform := [XSplit 1 (SLit (-32))].
Definition E_vr1 : sstate := Eval vm_compute in optS (apply_xforms E_vr_U xs_vr).
Definition E_vr1b : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1 1 (-32)).
Definition E_vr2 : sstate := Eval vm_compute in optS (unbase_obj_at E_vr1b 10 688).
Definition s_vr : wsub := Eval vm_compute in
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d LP.pi1); (16%positive, t_c LP.pi1);
   (17%positive, t_k LP.pi1); (18%positive, SLit 12)] ++ infer_sub 10 E_vr2 VRU.Pre_vr.
Definition R_vr : list sobj := Eval vm_compute in optR (entails_fr E_vr2 VRU.Pre_vr s_vr).
Definition T_keep0 : sstate := Eval vm_compute in T_after E_vr2 s_vr R_vr VRU.P_keep.
Definition T_fail0 : sstate := Eval vm_compute in T_after E_vr2 s_vr R_vr VRU.P_fail.
Definition T_grown0 : sstate := Eval vm_compute in T_after E_vr2 s_vr R_vr VRU.P_grown.
Definition xs_keep : list xform := [XRebase 2; XSelect [5; 1; 0; 6; 7; 8; 9; 10; 11; 12; 2; 13; 14; 3; 15; 16; 4; 17]%nat; XMerge 1].
Definition xs_grown : list xform := [XRebase 3; XSelect [5; 0; 2; 6; 7; 8; 9; 10; 11; 12; 3; 13; 14; 4; 15; 16; 1; 17]%nat; XMerge 1].
Definition T_keep0b : sstate := Eval vm_compute in optS (unbase_obj_at T_keep0 1 32).
Definition T_fail0b : sstate := Eval vm_compute in optS (unbase_obj_at T_fail0 1 32).
Definition T_grown0b : sstate := Eval vm_compute in optS (unbase_obj_at T_grown0 0 32).
Definition T_keep1 : sstate := Eval vm_compute in optS (apply_xforms T_keep0b xs_keep).
Definition T_fail1 : sstate := Eval vm_compute in optS (apply_xforms T_fail0b xs_keep).
Definition T_grown1 : sstate := Eval vm_compute in optS (apply_xforms T_grown0b xs_grown).
Definition nz_keep : list (positive * Z * positive) := [(300%positive, 12, 302%positive)].
Definition T_keep2 : sstate := Eval vm_compute in add_facts (TobjJVx.nz_facts nz_keep) T_keep1.
Definition tvG : list (sv * sv) := Eval vm_compute in
  import_tv (import_sub s_vr NF VRU.P_grown (ss_next E_vr2)) VRU.tv_post.

Lemma VTU_val : forall rho cv k, 0 <= k < 16 ->
  bv_unsigned (eval rho cv) <= bv_unsigned (eval rho xE0) -> bv_unsigned (eval rho xE0) <= 2 ^ 26 ->
  bv_unsigned (eval rho (VTU cv k)) = 16 * (bv_unsigned (eval rho xE0) - bv_unsigned (eval rho cv)) + k.
Proof.
  intros rho cv k Hk H1 H2. unfold VTU. cbn [eval].
  rewrite add_val, mul_val, sub_val, !lit_unsigned.
  pose proof (urange (eval rho cv)) as R1.
  rewrite (Z.mod_small 16) by lia. rewrite (Z.mod_small k) by lia.
  rewrite (Z.mod_small (bv_unsigned (eval rho xE0) - bv_unsigned (eval rho cv))) by lia.
  rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.

Section Sum.
Variable ok : world -> Prop.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis ML : malloc_laws segsU C_U.
Hypothesis MC : malloc_contracts segsU C_U EC_U.

Let nI : forall n : sstate * list (sv * sv), jnode := nodeI segsU C_U NP Kc rho0 (P0_hf FB) FB.
Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.
Let Q : assn := LQP segsU NP rho0 (Posts_hp_U Kc FB).

Definition cutsE : list edesc :=
  [(Pre_hp_U, LP.tvP_pre, (100, z0));
   (H60, LP.tvP, (90, VTU pP 2)); (H70, LP.tvP, (90, VTU pQ 1)); (HB8, LP.tvP, (90, VTU pQ 0));
   (T_pc1, LP.tvP, (90, VTU pC 14)); (T_da1, LP.tvP, (90, VTU pC 12));
   (T_keep2, LP.tvP, (90, VTU pC 9)); (T_grown1, tvG, (90, VTU pC 9)); (T_fail1, LP.tvP, (85, z0))].
Definition exitsE : list edesc :=
  [(E_pc_U, LP.tvP, (90, VTU pC 15)); (E_da, LP.tvP, (90, VTU pC 13)); (E_vr_U, LP.tvP, (90, VTU pC 10));
   (HPP_ret_U, LP.tvP, (0, z0))].
Lemma ejcert_ok : ejcert segsU NP FUEL_hp cutpcs_hp NP cutsE exitsE = true.
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma txt_extra_ok_U : forall rho kept R o a,
  P0_hf FB rho0 -> agree_vals NP rho0 rho -> In o R -> is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof using .
  intros rho kept R o a HP0 Hav Ho Ht Hr. unfold is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold xB, xL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 100%positive ltac:(reflexivity)), <- (Hw 101%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 101)) as R101.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply in_or_app; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 101))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)).

Hypothesis CPC : forall tv rho rho1,
  TR (SP segsU (fun tr md => JGv tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JGv tv rho tr md) (ss_next PCU.Pre_pc_U) rho1 PCU.Posts_pc_U).
Hypothesis CDA : forall tv rho rho1,
  TR (SP segsU (fun tr md => JGv tv rho tr md) DA.Pre_da rho1)
     (LQ segsU (fun tr md => JGv tv rho tr md) (ss_next DA.Pre_da) rho1 DA.Posts_da).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (PostsC segsU C_U Kc (fun _ => VRU.P0_vr) VRU.PD_vr FBc)).
Hypothesis REENTER : forall T tv rv rho b,
  In (T, tv, rv) cutsE -> 0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b -> TR (SPJ segsU (JGv tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b,
  In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hp_U Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Let PURE := pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre TR_callJ.
Let CLIENT := client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre TR_callP CVR.

Lemma meas_step : forall (S : sstate) rho rho' k,
  Forall (holds rho) (ss_facts S) -> In (SPUle pC xE0) (ss_facts S) -> In (SPUle xE0 xL) (ss_facts S) ->
  In (SPUle xL (SLit (2 ^ 26))) (ss_facts S) -> eval rho (VTU pC k) = eval rho' (VTU pC k) ->
  0 <= k -> k + 1 < 16 ->
  0 <= 90 * 2 ^ 64 + bv_unsigned (eval rho' (VTU pC k)) /\
  90 * 2 ^ 64 + bv_unsigned (eval rho' (VTU pC k)) < 90 * 2 ^ 64 + bv_unsigned (eval rho (VTU pC (k + 1))).
Proof using .
  intros S rho rho' k HF I1 I2 I3 Heq Hk1 Hk2.
  pose proof (proj1 (Forall_forall _ _) HF _ I1) as F1. pose proof (proj1 (Forall_forall _ _) HF _ I2) as F2.
  pose proof (proj1 (Forall_forall _ _) HF _ I3) as F3. cbn [holds] in F1, F2, F3.
  cbn [eval] in F3. rewrite lit_unsigned in F3. change ((2 ^ 26) mod 2 ^ 64) with (2 ^ 26) in F3.
  rewrite <- Heq.
  rewrite (VTU_val rho pC k), (VTU_val rho pC (k + 1)) by lia.
  pose proof (urange (eval rho pC)). lia.
Qed.

Ltac meas S := eapply (meas_step S); [eassumption | vm_compute; tauto | vm_compute; tauto | vm_compute; tauto |
  first [ eapply eval_agree; [eassumption | vm_compute; reflexivity]
        | eapply eval_agree_vals; [eassumption | vm_compute; reflexivity] ] | lia | lia].

Lemma X_P_ret : forall rho b, TR (SPJ segsU (JGv LP.tvP) HPP_ret_U rho) (FAM b).
Proof using POST nI. intros rho b. apply POST. cbn. tauto. Qed.

Lemma X_E_pc : forall rho, TR (SPJ segsU (JGv LP.tvP) E_pc_U rho) (FAM (emeas (E_pc_U, LP.tvP, (90, VTU pC 15)) rho)).
Proof using CPC PURE REENTER.
  intros rho. apply TR_facts. intros HF. eapply TR_pre.
  2: { apply (PURE E_pc2 PCU.Pre_pc_U s_pc R_pc PCU.Posts_pc_U rho LP.tvP _ (CPC LP.tvP rho));
         [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL Hag. destruct HinL as [<-|[]]; cbn [lf_state].
       replace (T_after E_pc2 s_pc R_pc PCU.P_ret_U) with T_pc0 by (vm_compute; reflexivity).
       apply (TR_pre (SPJ segsU (JGv LP.tvP) T_pc1 rho')).
       - intros w Hw. exact (SPJ_xforms segsU _ xs_pcm rho' T_pc0 T_pc1 w ltac:(vm_compute; reflexivity) Hw).
       - apply (REENTER T_pc1 LP.tvP (90, VTU pC 14) rho' _); [cbn [cutsE In]; tauto |].
         unfold emeas, ed_rank, ed_var; cbn [fst snd]. meas E_pc_U. }
  intros w Hw.
  apply (SPJ_unbase segsU _ rho E_pc1 1 (-108) E_pc2 w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ xs_pc rho E_pc_U E_pc1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_da : forall rho, TR (SPJ segsU (JGv LP.tvP) E_da rho) (FAM (emeas (E_da, LP.tvP, (90, VTU pC 13)) rho)).
Proof using CDA PURE REENTER.
  intros rho. apply TR_facts. intros HF. eapply TR_pre.
  2: { apply (PURE E_da1 DA.Pre_da s_da R_da DA.Posts_da rho LP.tvP _ (CDA LP.tvP rho));
         [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | ].
       intros L rho' HinL Hag. destruct HinL as [<-|[]]; cbn [lf_state].
       replace (T_after E_da1 s_da R_da DA.P_da) with T_da0 by (vm_compute; reflexivity).
       apply (TR_pre (SPJ segsU (JGv LP.tvP) T_da1 rho')).
       - intros w Hw. exact (SPJ_xforms segsU _ xs_dam rho' T_da0 T_da1 w ltac:(vm_compute; reflexivity) Hw).
       - apply (REENTER T_da1 LP.tvP (90, VTU pC 12) rho' _); [cbn [cutsE In]; tauto |].
         unfold emeas, ed_rank, ed_var; cbn [fst snd]. meas E_da. }
  intros w Hw. exact (SPJ_xforms segsU _ xs_da rho E_da E_da1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma X_E_vr : forall rho, TR (SPJ segsU (JGv LP.tvP) E_vr_U rho) (FAM (emeas (E_vr_U, LP.tvP, (90, VTU pC 10)) rho)).
Proof using CLIENT REENTER nI.
  intros rho. apply TR_facts. intros HF0. eapply TR_pre.
  2: { change (JGv LP.tvP) with (JGv ([] ++ LP.tvP)).
       apply (CLIENT E_vr2 s_vr R_vr rho [] LP.tvP _).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - reflexivity.
       - reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - intros Ai ms HF HP0 Hav _ _ _ HZ _ HT. split.
         + eapply robjs_checkF_sound with (extra := is_txt);
             [exact HF | exact (TobjJVx.T_ok_T0_agree _ _ _ _ Hav (@eq_refl comparison Lt) HT) | constructor | vm_compute; reflexivity |].
           intros o a Ho Hx Hr. eapply txt_extra_ok_U; eauto.
         + cbn beta. eapply (P0_vr_of_tvz rho 300 302 12); [reflexivity | reflexivity | exact HZ | | lia].
           eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto.
       - intros d rho' Hd Hag. destruct Hd as [<-|[<-|[<-|[]]]]; cbn [fst snd app].
         + replace (T_after E_vr2 s_vr R_vr VRU.P_keep) with T_keep0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_keep (ss_next E_vr2)) VRU.tv0) with LP.tvP by (vm_compute; reflexivity).
           apply (TR_pre (SPJ segsU (JGv LP.tvP) T_keep2 rho')).
           * intros w Hw.
             assert (W1 : SPJ segsU (JGv LP.tvP) T_keep1 rho' w).
             { apply (SPJ_xforms segsU _ xs_keep rho' T_keep0b T_keep1 w ltac:(vm_compute; reflexivity)).
               exact (SPJ_unbase segsU _ rho' T_keep0 1 32 T_keep0b w ltac:(vm_compute; reflexivity) Hw). }
             replace T_keep2 with (add_facts (TobjJVx.nz_facts nz_keep) T_keep1) by (vm_compute; reflexivity).
             apply SPJ_refacts_J; [exact W1 | vm_compute; reflexivity |].
             intros tr md HJ HFX.
             eapply (TobjJVx.nz_facts_sound segsU C_U NP Kc rho0 (P0_hf FB) FB (ss_facts T_keep1) LP.tvP);
               [vm_compute; reflexivity | exact HFX | exact HJ].
           * apply (REENTER T_keep2 LP.tvP (90, VTU pC 9) rho' _); [cbn [cutsE In]; tauto |].
             unfold emeas, ed_rank, ed_var; cbn [fst snd]. meas E_vr_U.
         + replace (T_after E_vr2 s_vr R_vr VRU.P_fail) with T_fail0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_fail (ss_next E_vr2)) VRU.tv0) with LP.tvP by (vm_compute; reflexivity).
           apply (TR_pre (SPJ segsU (JGv LP.tvP) T_fail1 rho')).
           * intros w Hw. apply (SPJ_xforms segsU _ xs_keep rho' T_fail0b T_fail1 w ltac:(vm_compute; reflexivity)).
             exact (SPJ_unbase segsU _ rho' T_fail0 1 32 T_fail0b w ltac:(vm_compute; reflexivity) Hw).
           * apply (REENTER T_fail1 LP.tvP (85, z0) rho' _); [cbn [cutsE In]; tauto |].
             unfold emeas, ed_rank, ed_var; cbn [fst snd].
             pose proof (urange (eval rho' z0)). pose proof (urange (eval rho (VTU pC 10))). lia.
         + replace (T_after E_vr2 s_vr R_vr VRU.P_grown) with T_grown0 by (vm_compute; reflexivity).
           replace (import_tv (import_sub s_vr NF VRU.P_grown (ss_next E_vr2)) VRU.tv_post) with tvG by (vm_compute; reflexivity).
           apply (TR_pre (SPJ segsU (JGv tvG) T_grown1 rho')).
           * intros w Hw. apply (SPJ_xforms segsU _ xs_grown rho' T_grown0b T_grown1 w ltac:(vm_compute; reflexivity)).
             exact (SPJ_unbase segsU _ rho' T_grown0 0 32 T_grown0b w ltac:(vm_compute; reflexivity) Hw).
           * apply (REENTER T_grown1 tvG (90, VTU pC 9) rho' _); [cbn [cutsE In]; tauto |].
             unfold emeas, ed_rank, ed_var; cbn [fst snd]. meas E_vr_U. }
  intros w Hw.
  apply (SPJ_unbase segsU _ rho E_vr1b 10 688 E_vr2 w ltac:(vm_compute; reflexivity)).
  apply (SPJ_unbase segsU _ rho E_vr1 1 (-32) E_vr1b w ltac:(vm_compute; reflexivity)).
  exact (SPJ_xforms segsU _ xs_vr rho E_vr_U E_vr1 w ltac:(vm_compute; reflexivity) Hw).
Qed.

Lemma exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) exitsE ->
  TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using CDA CLIENT CPC POST PURE REENTER nI.
  intros X tvX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_pc.
  - apply X_E_da.
  - apply X_E_vr.
  - apply X_P_ret.
Qed.
End SumT.

Section Safety.
Hypothesis PCS : PCU.parse_corner_sum_stmt_U.
Hypothesis DAS : DA.da_stmt_U.
Hypothesis VRS : VRU.vr_stmt_U.

Theorem handle_p_sum :
  triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvP_pre) Pre_hp_U rho0) (LQP segsU NP rho0 (Posts_hp_U Kc FB)).
Proof using HS MC ML PCS DAS VRS.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGE segsU C_U NP Kc rho0 (P0_hf FB) FB ML FUEL_hp cutpcs_hp NP cutsE exitsE ok Q (proj1 HS)
                (ejcert_jcert segsU NP _ _ _ _ _ ejcert_ok)) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nI (map (@edrop) cutsE)) w \/ Q w)
                (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
                (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_soundP segsU ok) (call_soundJ segsU ok)).
       - intros tv rho rho1. apply PCS.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros tv rho rho1. apply DAS.
         eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & _ & HK & _). exact HK.
       - intros FBc rho1. apply (VRS ok Kc FBc rho1 HS ML MC).
       - intros T tv rv rho b Hin _. exact (reenter_cutGE segsU C_U NP Kc rho0 (P0_hf FB) FB ok cutsE T tv rv Q rho Hin).
       - intros P tv rho b Hin. apply (exit_postG segsU C_U NP Kc (P0_hf FB) FB ok rho0 tv (Posts_hp_U Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis PCX : PCU.parse_corner_sum_ex_stmt_U.
Hypothesis DAX : DA.da_ex_stmt_U.
Hypothesis VRX : VRU.vr_ex_stmt_U.

Theorem handle_p_sum_ex :
  etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvP_pre) Pre_hp_U rho0) (LQP segsU NP rho0 (Posts_hp_U Kc FB)).
Proof using Hvi MCX ML PCX DAX VRX.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JG segsU C_U NP Kc rho0 (P0_hf FB) FB ML FUEL_hp cutpcs_hp NP cutsE exitsE Q ejcert_ok) with (rvT := (100, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeI segsU C_U NP Kc rho0 (P0_hf FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
                (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
                (call_completeP segsU) (call_completeJ segsU)).
       - intros tv rho rho1. apply PCX.
       - intros tv rho rho1. apply DAX.
       - intros FBc rho1. apply (VRX Kc FBc rho1 Hvi ML MCX).
       - intros T tv rv rho b Hin Hm. exact (ereenter_cutE segsU C_U NP Kc rho0 (P0_hf FB) FB cutsE T tv rv Q b rho Hin Hm).
       - intros P tv rho b Hin. apply (eexit_postG segsU C_U NP Kc (P0_hf FB) FB rho0 tv (Posts_hp_U Kc FB) P). exact Hin. }
  intros w Hw. apply JG_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem handle_p_sum_U (PCS : PCU.parse_corner_sum_stmt_U) (DAS : DA.da_stmt_U) (VRS : VRU.vr_stmt_U) :
  handle_p_sum_stmt_U.
Proof. intros ok Kc FB rho0 HS MC ML. exact (handle_p_sum ok Kc FB rho0 HS ML MC PCS DAS VRS). Qed.

Theorem handle_p_sum_ex_U (PCX : PCU.parse_corner_sum_ex_stmt_U) (DAX : DA.da_ex_stmt_U) (VRX : VRU.vr_ex_stmt_U) :
  handle_p_sum_ex_stmt_U.
Proof. intros Kc FB rho0 Hvi MCX ML. exact (handle_p_sum_ex Kc FB rho0 ML Hvi MCX PCX DAX VRX). Qed.
