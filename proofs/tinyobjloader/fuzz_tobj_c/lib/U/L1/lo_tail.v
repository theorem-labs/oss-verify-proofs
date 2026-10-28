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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue CursorGlue ObjXform ObjUnbase TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy TobjJVAz DrvGlue2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo_view lo4_common lo_tail_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo_entry.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_fs S_vf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require S_fu.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1 Lib_handle__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.
Module HFD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import LoT.

Lemma ejcert_ok : ejcertA segsU LD.NP 8000 cps LD.NP cutsE exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma perm_fs : permb LoU.tvL (LoV.keptL slots_fs ++ LoV.passedL slots_fs) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma perm_cv : permb LoU.tvL (LoV.keptL slots_cv ++ LoV.passedL slots_cv) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma perm_vf : permb LoU.tvL (LoV.keptL slots_vf ++ LoV.passedL slots_vf) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma view_fs : run_nsteps E_fs ns_fs = Some Ev_fs.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_cv : run_nsteps E_cv ns_cv = Some Ev_cv.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_fu : run_nsteps E_fu ns_fu = Some Ev_fu.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma view_vf0 : run_nsteps E_vf0 ns_vf0 = Some Ev_vf0.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf1 : run_nsteps E_vf1 ns_vf1 = Some Ev_vf1.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf2 : run_nsteps E_vf2 ns_vf2 = Some Ev_vf2.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf3 : run_nsteps E_vf3 ns_vf3 = Some Ev_vf3.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf4 : run_nsteps E_vf4 ns_vf4 = Some Ev_vf4.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf5 : run_nsteps E_vf5 ns_vf5 = Some Ev_vf5.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf6 : run_nsteps E_vf6 ns_vf6 = Some Ev_vf6.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma view_vf7 : run_nsteps E_vf7e ns_vf7 = Some Ev_vf7.
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma chk_fs : site_check C_U LD.NP S_fs.Pre_fs S_fs.tv0 S_fs.ahd S_fs.PDA_fs S_fs.FD.NP LoU.base_facts LD.is_txt
  Ev_fs s_fs (LoV.keptL slots_fs) (LoV.passedL slots_fs) LoU.amL 395 z0 conts_fs = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_cv : site_check C_U LD.NP S_vr.Pre_vr S_vr.tv0 (AHead (SVar 99)) (PDAh S_vr.PD_vr 99) 100 LoU.base_facts LD.is_txt
  Ev_cv s_cv (LoV.keptL slots_cv) (LoV.passedL slots_cv) LoU.amL 380 (LD.VCp 4) conts_cv = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf0 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf0 s_vf0 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 370 z0 conts_vf0 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf1 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf1 s_vf1 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 360 z0 conts_vf1 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf2 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf2 s_vf2 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 350 z0 conts_vf2 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf3 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf3 s_vf3 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 340 z0 conts_vf3 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf4 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf4 s_vf4 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 330 z0 conts_vf4 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf5 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf5 s_vf5 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 320 z0 conts_vf5 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf6 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf6 s_vf6 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 300 z0 conts_vf6 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_vf7 : site_check C_U LD.NP S_vf.Pre_vf S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF LoU.base_facts LD.is_txt
  Ev_vf7 s_vf7 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 290 z0 conts_vf7 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.site_check_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition emp7z : sobj := Eval vm_compute in nth (find_empty 0 (ss_objs T_vf7z)) (ss_objs T_vf7z) empty0.
Definition emp7f : sobj := Eval vm_compute in nth (find_empty 0 (ss_objs T_vf7f)) (ss_objs T_vf7f) empty0.
Definition emp7o : sobj := Eval vm_compute in nth (find_empty 0 (ss_objs T_vf7o)) (ss_objs T_vf7o) empty0.
Lemma drop7z : drop_empty T_vf7z = T_vf7zx.
Proof. vm_compute. reflexivity. Qed.
Lemma drop7f : drop_empty T_vf7f = T_vf7fx.
Proof. vm_compute. reflexivity. Qed.
Lemma drop7o : drop_empty T_vf7o = T_vf7ox.
Proof. vm_compute. reflexivity. Qed.

Lemma T_fu0_eq : add_facts (ss_facts Ev_fu) (import_post s_fu (ss_next S_fu.Pre_fu_U) S_fu.P_fu_U (ss_next Ev_fu) R_fu) = T_fu0.
Proof. vm_compute. reflexivity. Qed.

(* vf's P0 (a nonempty vector's data is a block of FBc) for a vector whose data block is tracked in kept *)
Lemma P0_vf_kept : forall (FB : list (Z * Z)) rho d (c : sv) k e R ms s kept,
  wsub_get s 15%positive = SVar d -> wsub_get s 16%positive = c -> wsub_get s 17%positive = SVar k ->
  wsub_get s 18%positive = SLit e -> 1 <= e <= 4096 ->
  In (SVar d, SMd M_MUL (SLit e) (SVar k)) kept -> tvz rho kept ->
  holds rho (SPUle c (SVar k)) -> holds rho (SPUle (SVar k) (SLit (2 ^ 47))) ->
  S_vf.P0_vf (FBx FB rho kept) (rho_sub (rho_absorb rho R ms) s).
Proof.
  intros FB rho d c k e R ms s kept H15 H16 H17 H18 He Hin HZ Hck Hk.
  unfold S_vf.P0_vf, S_vf.kbytes, S_vf.vE, S_vf.vK.
  assert (Hm : eval (rho_sub (rho_absorb rho R ms) s) (SMd M_MUL (SVar 18) (SVar 17)) = eval rho (SMd M_MUL (SLit e) (SVar k)))
    by (cbn [eval]; rewrite !rw_call', H17, H18; reflexivity).
  rewrite Hm, !rw_call', H15, H16. intros Hc.
  apply (proj1 (holds_ule _ _ _)) in Hck. apply (proj1 (holds_ule _ _ _)) in Hk.
  rewrite U_lit in Hk. rewrite !eval_var in *. unfold M64v in *. rewrite (Z.mod_small (2 ^ 47)) in Hk by lia.
  pose proof (bv_urange (rw rho k)) as Rk. pose proof (bv_urange (eval rho c)) as Rc.
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

Lemma P0_vf_zero : forall FB rho R ms s, wsub_get s 16%positive = SLit 0 -> S_vf.P0_vf FB (rho_sub (rho_absorb rho R ms) s).
Proof. intros FB rho R ms s H16. unfold S_vf.P0_vf. rewrite rw_call', H16, U_lit. intros H. exfalso. apply H. reflexivity. Qed.

Lemma meas_rank : forall (X Y : sstate) tx ty ax ay r1 r2 rho rho',
  0 <= r1 -> r1 < r2 -> 0 <= ameas ((X, (tx, ax)), (r1, z0)) rho' < ameas ((Y, (ty, ay)), (r2, z0)) rho.
Proof.
  intros. unfold ameas, ad_rank, ad_var. cbn [fst snd].
  pose proof (urange (eval rho' z0)). pose proof (urange (eval rho z0)). nia.
Qed.

Section Sum.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am.
Let Q : assn := LQP segsU LD.NP rho0 (Posts_loF_U Kc FB).

Lemma JGv_tvz : forall tv am rho tr md, JGv tv am rho tr md -> tvz rho tv.
Proof. intros tv am rho tr md (Ai & (_ & _ & _ & _ & (_ & _ & Hz) & _) & _). exact Hz. Qed.

(* After a kept reservation (count + 3 <= cap) the acol data block is nonempty, so its block facts hold. *)
Lemma keep_facts : forall rho tr md, JGv tvT_cv1 LoU.amL rho tr md -> Forall (holds rho) (ss_facts T_cv1) ->
  Forall (holds rho) (tv_facts acol_blk).
Proof.
  intros rho tr md HJ HF.
  assert (Hin : In acol_blk tvT_cv1) by (vm_compute; tauto).
  eapply (JGA_tv_facts segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB); [exact HJ | exact Hin |].
  pose proof (proj1 (Forall_forall _ _) (JGv_tvz _ _ _ _ _ HJ) _ Hin) as Hz.
  intros H0. specialize (Hz (fun N => N H0)). clear H0. revert Hz. unfold tvv, acol_blk. cbn [fst snd].
  pick_facts HF [118%nat; 124%nat; 126%nat]. zfacts. nia.
Qed.

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
Hypothesis TR_callJ : forall (J Jp Jp' Jc' : jpred) (C0 Pre : sstate) (s : wsub) (R : list sobj) (Posts : list leaf)
  (Q' : assn) (rho : valuation),
  entails_fr C0 Pre s = Some R -> call_check C0 Pre s R Posts = true ->
  (forall rho1 : valuation, TR (SPJ segsU Jp Pre rho1) (LQJ segsU Jp' (ss_next Pre) rho1 Posts)) ->
  (forall tr ms md, smatch segsU rho C0 (tr, mkCfg ms md) -> J rho tr md -> Jp (rho_sub (rho_absorb rho R ms) s) tr md) ->
  (forall L rho' rhoL tr ms md tr' md', In L Posts -> smatch segsU rho C0 (tr, mkCfg ms md) -> J rho tr md ->
     call_link rho ms R s Pre C0 (lf_state L) rho' rhoL -> Jp' rhoL tr' md' -> Jc' rho' tr' md') ->
  (forall L rho', In L Posts -> agree_below (ss_next C0) rho rho' ->
     TR (SPJ segsU Jc' (import_post s (ss_next Pre) (lf_state L) (ss_next C0) R) rho') Q') ->
  TR (SPJ segsU J C0 rho) Q'.

Hypothesis CFS : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_fs.P0_fs FBc) FBc S_fs.tv0 S_fs.ahd) S_fs.Pre_fs rho1)
     (LQP segsU S_fs.FD.NP rho1 (PostsCA segsU C_U Kc S_fs.P0_fs S_fs.PDA_fs FBc)).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc ((fun _ : list (Z * Z) => S_vr.P0_vr) FBc) FBc S_vr.tv0 (AHead (SVar 99))) S_vr.Pre_vr rho1)
     (LQP segsU 100 rho1 (PostsCA segsU C_U Kc (fun _ : list (Z * Z) => S_vr.P0_vr) (PDAh S_vr.PD_vr 99) FBc)).
Hypothesis CVF : forall FBc rho1,
  TR (SPJ segsU (JGA_pre segsU C_U Kc (S_vf.P0_vf FBc) FBc S_vf.tv0 S_vf.ahd) S_vf.Pre_vf rho1)
     (LQP segsU NF rho1 (PostsCA segsU C_U Kc S_vf.P0_vf S_vf.PDA_vf FBc)).
Hypothesis CFU : forall tv am rho rho1,
  TR (SP segsU (fun tr md => JGv tv am rho tr md) S_fu.Pre_fu_U rho1)
     (LQ segsU (fun tr md => JGv tv am rho tr md) (ss_next S_fu.Pre_fu_U) rho1 S_fu.Posts_fu_U).
Hypothesis KBD : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_bd rho) (FAM b).
Hypothesis REENTER : forall (i : nat) (T : sstate) (tv : list (sv * sv)) (am : amode) (rv : Z * sv) (rho : valuation) (b : Z),
  nth_error cutsE i = Some ((T, (tv, am)), rv) -> 0 <= ameas ((T, (tv, am)), rv) rho < b ->
  TR (SPJ segsU (JGv tv am) T rho) (FAM b).

Let PURE := pure_callAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML TR TR_facts TR_pre TR_callJ.

Lemma X_fs : forall rho, TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_fs rho) (FAM (ameas ((E_fs, (LoU.tvL, LoU.amL)), (395, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_fs, (LoU.tvL, LoU.amL)), (395, z0)) rho) with (emeasZ 395 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_fs rho w (permb_sound _ _ perm_fs)).
    exact (SPJ_nsteps segsU _ ns_fs rho E_fs Ev_fs w view_fs Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_fs.P0_fs S_fs.Pre_fs
            S_fs.tv0 S_fs.ahd S_fs.PDA_fs S_fs.FD.NP eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CFS (txt_extra_ok_U FB rho0))
           Ev_fs s_fs (LoV.keptL slots_fs) (LoV.passedL slots_fs) LoU.amL 395 z0 conts_fs rho _ chk_fs).
  - intros ms R HF HP0 Hav HZ. exact I.
  - intros c rho' Hc Hm. unfold conts_fs in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 1 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 2 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 3 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 4 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_cv : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_cv rho) (FAM (ameas ((E_cv, (LoU.tvL, LoU.amL)), (380, LD.VCp 4)) rho)).
Proof.
  intros rho. change (ameas ((E_cv, (LoU.tvL, LoU.amL)), (380, LD.VCp 4)) rho) with (emeasZ 380 (LD.VCp 4) rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_cv rho w (permb_sound _ _ perm_cv)).
    exact (SPJ_nsteps segsU _ ns_cv rho E_cv Ev_cv w view_cv Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr
            S_vr.tv0 (AHead (SVar 99)) (PDAh S_vr.PD_vr 99) 100 eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVR (txt_extra_ok_U FB rho0))
           Ev_cv s_cv (LoV.keptL slots_cv) (LoV.passedL slots_cv) LoU.amL 380 (LD.VCp 4) conts_cv rho _ chk_cv).
  - intros ms R HF HP0 Hav HZ. cbn beta.
    eapply (HFD.P0_vr_of_tvz rho 125 127 4 R ms s_cv); [vm_compute; reflexivity | vm_compute; reflexivity | | | lia].
    { eapply (LG.tvz_one rho _ _ HZ). apply in_or_app. right. left. reflexivity. }
    { eapply (proj1 (Forall_forall _ _) HF). vm_compute. tauto. }
  - intros c rho' Hc Hm. unfold conts_cv in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + eapply TR_pre; [ | exact (REENTER 6 T_cv1x tvT_cv1 LoU.amL (380, LD.VCp 2) rho' _ eq_refl Hm) ].
      intros w Hw. unfold T_cv1x. apply (SPJ_refacts_J segsU _ rho' T_cv1 (tv_facts acol_blk) w Hw); [vm_compute; reflexivity |].
      intros tr md HJ HF. exact (keep_facts rho' tr md HJ HF).
    + exact (REENTER 7 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 8 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf0 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf0 rho) (FAM (ameas ((E_vf0, (LoU.tvL, LoU.amL)), (370, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf0, (LoU.tvL, LoU.amL)), (370, z0)) rho) with (emeasZ 370 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf0 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf0 rho E_vf0 Ev_vf0 w view_vf0 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf0 s_vf0 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 370 z0 conts_vf0 rho _ chk_vf0).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [31%nat; 34%nat].
    eapply (P0_vf_kept FB rho 110 (SMd M_MUL (SVar 111) (SLit 3)) 112 4 R ms s_vf0 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf0 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 10 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 11 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 12 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf1 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf1 rho) (FAM (ameas ((E_vf1, (LoU.tvL, LoU.amL)), (360, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf1, (LoU.tvL, LoU.amL)), (360, z0)) rho) with (emeasZ 360 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf1 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf1 rho E_vf1 Ev_vf1 w view_vf1 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf1 s_vf1 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 360 z0 conts_vf1 rho _ chk_vf1).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [37%nat; 39%nat].
    eapply (P0_vf_kept FB rho 113 (SVar 114) 115 4 R ms s_vf1 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf1 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 13 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 14 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 15 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf2 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf2 rho) (FAM (ameas ((E_vf2, (LoU.tvL, LoU.amL)), (350, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf2, (LoU.tvL, LoU.amL)), (350, z0)) rho) with (emeasZ 350 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf2 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf2 rho E_vf2 Ev_vf2 w view_vf2 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf2 s_vf2 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 350 z0 conts_vf2 rho _ chk_vf2).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [42%nat; 44%nat].
    eapply (P0_vf_kept FB rho 116 (SVar 117) 118 4 R ms s_vf2 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf2 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 16 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 17 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 18 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf3 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf3 rho) (FAM (ameas ((E_vf3, (LoU.tvL, LoU.amL)), (340, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf3, (LoU.tvL, LoU.amL)), (340, z0)) rho) with (emeasZ 340 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf3 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf3 rho E_vf3 Ev_vf3 w view_vf3 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf3 s_vf3 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 340 z0 conts_vf3 rho _ chk_vf3).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [47%nat; 49%nat].
    eapply (P0_vf_kept FB rho 119 (SVar 120) 121 4 R ms s_vf3 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf3 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 19 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 20 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 21 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf4 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf4 rho) (FAM (ameas ((E_vf4, (LoU.tvL, LoU.amL)), (330, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf4, (LoU.tvL, LoU.amL)), (330, z0)) rho) with (emeasZ 330 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf4 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf4 rho E_vf4 Ev_vf4 w view_vf4 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf4 s_vf4 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 330 z0 conts_vf4 rho _ chk_vf4).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [52%nat; 54%nat].
    eapply (P0_vf_kept FB rho 122 (SVar 123) 124 4 R ms s_vf4 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf4 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 22 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 23 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 24 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf5 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf5 rho) (FAM (ameas ((E_vf5, (LoU.tvL, LoU.amL)), (320, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf5, (LoU.tvL, LoU.amL)), (320, z0)) rho) with (emeasZ 320 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf5 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf5 rho E_vf5 Ev_vf5 w view_vf5 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf5 s_vf5 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 320 z0 conts_vf5 rho _ chk_vf5).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [57%nat; 59%nat].
    eapply (P0_vf_kept FB rho 125 (SVar 126) 127 4 R ms s_vf5 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf5 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 25 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 26 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 27 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf6 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf6 rho) (FAM (ameas ((E_vf6, (LoU.tvL, LoU.amL)), (300, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf6, (LoU.tvL, LoU.amL)), (300, z0)) rho) with (emeasZ 300 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf6 rho w (permb_sound _ _ perm_vf)).
    exact (SPJ_nsteps segsU _ ns_vf6 rho E_vf6 Ev_vf6 w view_vf6 Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf6 s_vf6 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 300 z0 conts_vf6 rho _ chk_vf6).
  - intros ms R HF HP0 Hav HZ. pick_facts HF [62%nat; 64%nat].
    eapply (P0_vf_kept FB rho 128 (SVar 129) 130 128 R ms s_vf6 (LoV.keptL slots_vf));
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia
      | vm_compute; tauto | exact (tvz_app_l _ _ _ HZ) | assumption | assumption].
  - intros c rho' Hc Hm. unfold conts_vf6 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + exact (REENTER 28 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 29 _ _ _ _ rho' _ eq_refl Hm).
    + exact (REENTER 30 _ _ _ _ rho' _ eq_refl Hm).
Qed.

Lemma X_vf7 : forall rho,
  TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_vf7 rho) (FAM (ameas ((E_vf7, (LoU.tvL, LoU.amL)), (290, z0)) rho)).
Proof.
  intros rho. change (ameas ((E_vf7, (LoU.tvL, LoU.amL)), (290, z0)) rho) with (emeasZ 290 z0 rho).
  eapply TR_pre.
  { intros w Hw. apply (SPJ_JGA_perm segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoU.tvL _ LoU.amL Ev_vf7 rho w (permb_sound _ _ perm_vf)).
    apply (SPJ_nsteps segsU _ ns_vf7 rho E_vf7e Ev_vf7 w view_vf7).
    exact (SPJ_add_empties segsU _ rho E_vf7 [empty0] w ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hw). }
  apply ((client_siteAT segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML (TobjJVA.NP_ok_intro LD.NP eq_refl) S_vf.P0_vf S_vf.Pre_vf
            S_vf.tv0 S_vf.ahd S_vf.PDA_vf NF eq_refl LoU.base_facts LD.is_txt TR TR_facts TR_ex TR_pre TR_callP
            CVF (txt_extra_ok_U FB rho0))
           Ev_vf7 s_vf7 (LoV.keptL slots_vf) (LoV.passedL slots_vf) LoU.amL 290 z0 conts_vf7 rho _ chk_vf7).
  - intros ms R HF HP0 Hav HZ. apply P0_vf_zero. vm_compute. reflexivity.
  - intros c rho' Hc Hm. unfold conts_vf7 in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[]]]]; cbn [fst snd ad_tv ad_am ad_state] in Hm |- *.
    + eapply TR_pre; [ | exact (REENTER 31 T_vf7zx tvT_vf7z amT_vf7z (285, z0) rho' _ eq_refl Hm) ].
      intros w Hw. rewrite <- drop7z. unfold drop_empty.
      apply (SPJ_drop_empty segsU _ rho' T_vf7z (find_empty 0 (ss_objs T_vf7z)) emp7z w);
        [vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw].
      intros tr md _ _. vm_compute. first [lia | discriminate | intros Hq; discriminate Hq].
    + eapply TR_pre; [ | exact (REENTER 32 T_vf7fx tvT_vf7f amT_vf7f (285, z0) rho' _ eq_refl Hm) ].
      intros w Hw. rewrite <- drop7f. unfold drop_empty.
      apply (SPJ_drop_empty segsU _ rho' T_vf7f (find_empty 0 (ss_objs T_vf7f)) emp7f w);
        [vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw].
      intros tr md _ _. vm_compute. first [lia | discriminate | intros Hq; discriminate Hq].
    + eapply TR_pre; [ | exact (REENTER 33 T_vf7ox tvT_vf7o amT_vf7o (285, z0) rho' _ eq_refl Hm) ].
      intros w Hw. rewrite <- drop7o. unfold drop_empty.
      apply (SPJ_drop_empty segsU _ rho' T_vf7o (find_empty 0 (ss_objs T_vf7o)) emp7o w);
        [vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw].
      intros tr md _ _. vm_compute. first [lia | discriminate | intros Hq; discriminate Hq].
Qed.

Lemma X_fu : forall rho, TR (SPJ segsU (JGv LoU.tvL LoU.amL) E_fu rho) (FAM (ameas ((E_fu, (LoU.tvL, LoU.amL)), (310, z0)) rho)).
Proof.
  intros rho.
  apply (TR_pre (SPJ segsU (JGv LoU.tvL LoU.amL) Ev_fu rho)).
  { intros w Hw. exact (SPJ_nsteps segsU _ ns_fu rho E_fu Ev_fu w view_fu Hw). }
  apply (PURE Ev_fu S_fu.Pre_fu_U s_fu R_fu S_fu.Posts_fu_U rho LoU.tvL LoU.amL _ (CFU LoU.tvL LoU.amL rho)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros L rho' HL _. destruct HL as [<-|[]]. cbn [lf_state]. rewrite T_fu0_eq.
    eapply TR_pre; [ | exact (REENTER 9 T_fu LoU.tvL LoU.amL (305, z0) rho' _ eq_refl (meas_rank _ _ _ _ _ _ 305 310 rho rho' ltac:(lia) ltac:(lia))) ].
    intros w Hw. apply (SPJ_renormK segsU _ LoU.base_facts (LoV.renorm_prog T_fu0) T_fu0 T_fu rho' w);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hw].
Qed.

Lemma exits_ok_all : Forall (fun e => forall rho, TR (SPJ segsU (JGv (ad_tv e) (ad_am e)) (ad_state e) rho) (FAM (ameas e rho))) exitsE.
Proof.
  unfold exitsE.
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_fs |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_cv |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf0 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf1 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf2 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf3 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf4 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf5 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf6 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_vf7 |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; exact X_fu |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KBD |].
  apply Forall_nil.
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof.
  intros X tvX amX rvX rho Hin. exact (proj1 (Forall_forall _ _) exits_ok_all _ Hin rho).
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis FS : S_fs.fs_stmt_U.
Hypothesis VR : S_vr.vr_stmt_U.
Hypothesis VF : S_vf.vf_stmt_U.
Hypothesis FU : S_fu.finalize_unknowns_sum_stmt_U.
Hypothesis BD : lo_entry.K_stmt LoU.K_bd.

Theorem lo_tail_S : forall rho, triple segsU ok (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_tail rho) Q.
Proof.
  intros rho.
  apply (cfg_sound_JGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML 8000 cps LD.NP cutsE exitsE ok Q (proj1 HS)
           (ejcertA_jcertA segsU LD.NP _ _ _ _ _ ejcert_ok)) with (rvT := (400, z0)); [|left; reflexivity].
  apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) cutsE)) w \/ Q w)
           (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
           (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_soundP segsU ok) (call_soundJ segsU ok)).
  - intros FBc rho1. exact (FS ok Kc FBc rho1 HS ML MC).
  - intros FBc rho1. apply (JGA_frame_sum segsU C_U Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 S_vr.PD_vr 100 99 ML);
      [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; exact (VR ok Kc FBc' rho1' HS ML MC)].
  - intros FBc rho1. exact (VF ok Kc FBc rho1 HS ML MC).
  - intros tv am rho' rho1. apply FU. eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
  - intros rho' b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (BD ok Kc FB rho0 HS ML MC rho').
  - intros i T tv am rv rho' b Hi _.
    exact (reenter_cutGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ok cutsE T tv am rv Q rho' ltac:(eapply nth_error_In; exact Hi)).
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis FSX : S_fs.fs_ex_stmt_U.
Hypothesis VRX : S_vr.vr_ex_stmt_U.
Hypothesis VFX : S_vf.vf_ex_stmt_U.
Hypothesis FUX : S_fu.finalize_unknowns_sum_ex_stmt_U.
Hypothesis BDX : lo_entry.K_ex_stmt LoU.K_bd.

Theorem lo_tail_E : forall rho, etriple segsU (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_tail rho) Q.
Proof.
  intros rho.
  apply (cfg_complete_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML 8000 cps LD.NP cutsE exitsE Q ejcert_ok)
    with (rvT := (400, z0)); [|left; reflexivity].
  apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB) cutsE) b w \/ Q w)
           (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
           (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_completeP segsU) (call_completeJ segsU)).
  - intros FBc rho1. exact (FSX Kc FBc rho1 Hvi ML MCX).
  - intros FBc rho1. apply (JGA_frame_sum_ex segsU C_U Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 S_vr.PD_vr 100 99 ML);
      [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; exact (VRX Kc FBc' rho1' Hvi ML MCX)].
  - intros FBc rho1. exact (VFX Kc FBc rho1 Hvi ML MCX).
  - intros tv am rho' rho1. apply FUX.
  - intros rho' b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (BDX Kc FB rho0 Hvi ML MCX rho').
  - intros i T tv am rv rho' b Hi Hm.
    apply (ereenter_cutAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB cutsE T tv am rv Q b rho' ltac:(eapply nth_error_In; exact Hi)).
    exact Hm.
Qed.
End Existence.
End Sum.

Theorem lo_tail_K_U : S_fs.fs_stmt_U -> S_vr.vr_stmt_U -> S_vf.vf_stmt_U -> S_fu.finalize_unknowns_sum_stmt_U ->
  lo_entry.K_stmt LoU.K_bd -> lo_entry.K_stmt LoU.K_tail.
Proof.
  intros FS VR VF FU BD ok Kc FB rho0 HS ML MC rho.
  exact (lo_tail_S Kc FB rho0 ML ok HS MC FS VR VF FU BD rho).
Qed.

Theorem lo_tail_K_ex_U : S_fs.fs_ex_stmt_U -> S_vr.vr_ex_stmt_U -> S_vf.vf_ex_stmt_U -> S_fu.finalize_unknowns_sum_ex_stmt_U ->
  lo_entry.K_ex_stmt LoU.K_bd -> lo_entry.K_ex_stmt LoU.K_tail.
Proof.
  intros FSX VRX VFX FUX BDX Kc FB rho0 Hvi ML MCX rho.
  exact (lo_tail_E Kc FB rho0 ML Hvi MCX FSX VRX VFX FUX BDX rho).
Qed.
