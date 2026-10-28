From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV DrvLoop.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PA := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith.
Module PG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue.

(* A parse_corner call from handle_f on segsU.  The exit state E is split by xs1 so that object ks is the
   corner slot [12 pA, 12 pA + 12) of the corners data (P's off12A/off12A12); the slot is reshaped to P's
   slot_obj (base t_d co1 + 12 pA) for Pre_pc_U.  After the call the slot (object ko of the post) is reshaped back
   to P's mid_obj and xs2 normalizes the post, which must entail the cut TP. *)
Definition pc_post (E2 : sstate) (s : wsub) (R : list sobj) (L : leaf) : sstate :=
  add_facts (ss_facts E2) (import_post s NF (lf_state L) (ss_next E2) R).

Definition pc_site_checkU (E : sstate) (xs1 : list xform) (ks ko : nat) (xs2 : list xform)
    (TP : sstate) (vP : sv) (rP rE : Z) (vE : sv) : bool :=
  match apply_xforms E xs1 with
  | Some S1 =>
      PG.obj_shape S1 ks (t_d co1) PA.off12A PA.off12A12 && obj_wf (ss_next S1) PA.slot_obj &&
      PG.pc_need_facts (ss_facts S1) &&
      let E2 := reshape_obj_at S1 ks PA.slot_obj in
      let s := infer_sub 10 E2 PCU.Pre_pc_U in
      match entails_fr E2 PCU.Pre_pc_U s with
      | Some R =>
          call_check E2 PCU.Pre_pc_U s R PCU.Posts_pc_U && Pos.leb NP (ss_next E2) &&
          tv_below (ss_next E2) tvH && forallb (sprop_below (ss_next E2)) (ss_facts E2) &&
          forallb (fun L =>
            let C := pc_post E2 s R L in
            PG.obj_shape C ko (ob_base PA.slot_obj) (SLit 0) (SLit 12) && obj_wf (ss_next C) PA.mid_obj &&
            PG.pc_need_facts (ss_facts C) &&
            match apply_xforms (reshape_obj_at C ko PA.mid_obj) xs2 with
            | Some X => TobjJVx.entE_check NP (ss_next E2) X TP tvH tvH vP rP rE vE
            | None => false
            end) PCU.Posts_pc_U
      | None => false
      end
  | None => false
  end.

Section PcSite.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn),
  (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Ltac argty f := let t := type of f in lazymatch t with forall _ : ?A, _ => exact A end.
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)).
Hypothesis CPC : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PCU.Posts_pc_U).
Variable CUTS : list edesc.
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) CUTS ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).

Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.
Let PURE := pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre TR_callJ.
Let ENT := TobjJVx.entE_TR segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma X_pc_site : forall (E : sstate) (xs1 : list xform) (ks ko : nat) (xs2 : list xform)
    (TP : sstate) (vP : sv) (rP rE : Z) (vE : sv) (rho : valuation),
  pc_site_checkU E xs1 ks ko xs2 TP vP rP rE vE = true ->
  In (TP, tvH, (rP, vP)) CUTS ->
  TR (SPJ segsU (JGv tvH) E rho) (FAM (emeas (E, tvH, (rE, vE)) rho)).
Proof.
  intros E xs1 ks ko xs2 TP vP rP rE vE rho H HTP. unfold pc_site_checkU in H.
  destruct (apply_xforms E xs1) as [S1|] eqn:X1; [|discriminate].
  apply andb_prop in H as [H Hrest]. apply andb_prop in H as [H Hnf]. apply andb_prop in H as [Hsh Hwf].
  destruct (PG.obj_shapeP _ _ _ _ _ Hsh) as (o & Ho & Hb & Hl & Hh & Hd).
  apply PG.pc_need_factsP in Hnf as [F1 F2].
  cbv zeta in Hrest.
  destruct (entails_fr (reshape_obj_at S1 ks PA.slot_obj) PCU.Pre_pc_U
              (infer_sub 10 (reshape_obj_at S1 ks PA.slot_obj) PCU.Pre_pc_U)) as [R|] eqn:HE; [|discriminate].
  apply andb_prop in Hrest as [Hrest HP]. apply andb_prop in Hrest as [Hrest C4].
  apply andb_prop in Hrest as [Hrest C3]. apply andb_prop in Hrest as [C1 C2].
  rewrite (TobjJVx.emeas_emeasZ E tvH rE vE rho).
  eapply TR_pre.
  2: { apply (PURE (reshape_obj_at S1 ks PA.slot_obj) PCU.Pre_pc_U
                (infer_sub 10 (reshape_obj_at S1 ks PA.slot_obj) PCU.Pre_pc_U) R PCU.Posts_pc_U rho tvH _
                (CPC tvH rho) HE C1 C2 C3 C4).
       intros L rho' HinL Hag.
       pose proof (proj1 (forallb_forall _ _) HP L HinL) as HL. cbv beta in HL.
       apply andb_prop in HL as [HL Hc]. apply andb_prop in HL as [HL Hnf2]. apply andb_prop in HL as [Hsh2 Hwf2].
       destruct (PG.obj_shapeP _ _ _ _ _ Hsh2) as (o2 & Ho2 & Hb2 & Hl2 & Hh2 & Hd2).
       apply PG.pc_need_factsP in Hnf2 as [G1 G2].
       destruct (apply_xforms (reshape_obj_at (pc_post (reshape_obj_at S1 ks PA.slot_obj)
                   (infer_sub 10 (reshape_obj_at S1 ks PA.slot_obj) PCU.Pre_pc_U) R L) ko PA.mid_obj) xs2)
         as [X|] eqn:X2; [|discriminate].
       eapply TR_pre.
       2: { eapply (ENT _ X TP tvH tvH tvH _ _ _ _ rho rho' _ Hc (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
            intros rho'' Hm. apply (REENTER TP tvH (rP, vP) rho''); [exact HTP |].
            rewrite TobjJVx.emeas_emeasZ. exact Hm. }
       intros w Hw. eapply SPJ_xforms; [exact X2 |].
       eapply (SPJ_reshape segsU _ rho' _ ko o2 PA.mid_obj w Ho2 eq_refl eq_refl Hd2 Hwf2); [|exact Hw].
       intros HF. destruct (PA.slot_eqs rho' _ HF G1 G2) as [Q1 Q2]. revert Q1 Q2.
       unfold obj_lo_of, obj_hi_of. rewrite Hb2, Hl2, Hh2. unfold PA.slot_obj, PA.mid_obj. cbn [ob_base ob_lo ob_hi].
       intros Q1 Q2. lia. }
  intros w Hw.
  eapply (SPJ_reshape segsU _ rho S1 ks o PA.slot_obj w Ho eq_refl eq_refl Hd Hwf).
  2: { eapply SPJ_xforms; [exact X1 | exact Hw]. }
  intros HF. destruct (PA.slot_eqs rho _ HF F1 F2) as [Q1 Q2]. revert Q1 Q2.
  unfold obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. unfold PA.slot_obj, PA.mid_obj. cbn [ob_base ob_lo ob_hi].
  intros Q1 Q2. lia.
Qed.

End PcSite.
