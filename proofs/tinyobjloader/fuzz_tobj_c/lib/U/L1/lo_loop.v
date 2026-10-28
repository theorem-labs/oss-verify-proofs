From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import
  SumConv CfgGlue ObjXform TobjJV TobjJVx TobjJVA TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo4_meas lo_front lo_ret_defs lo_nodes lo4_callees.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo_entry.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_bw lo4_bwda lo4_da0 lo4_da1 lo4_da2 lo4_fs lo4_hf lo4_hl.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_hp lo4_hvn lo4_ir lo4_mf lo4_ml lo4_nt lo4_op1 lo4_op3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_op3b lo4_sdA1 lo4_sdA2 lo4_sdA3 lo4_sdA4 lo4_sdA5 lo4_sdA6 lo4_sdA7.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_sdA8 lo4_sdB1 lo4_sdB2 lo4_sdB3 lo4_se1 lo4_se2 lo4_se3 lo4_se4.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_se5 lo4_se6 lo4_se7 lo4_se8 lo4_se9 lo4_si lo4_vrA lo4_vrB.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require S_hl S_hp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require S_hf S_bw.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require S_hvn S_op S_u18350.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L14 Require S_ir.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_fs S_ml.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_da.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require S_mf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require S_nt S_si S_sd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_handle__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module HFD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

Lemma ejcert_ok : ejcertA segsU LD.NP LoNodes.FUEL LoNodes.cps LD.NP LoNodes.cutsE LoNodes.exitsE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* membership of a node in a list of named nodes, by syntactic comparison *)
Ltac in_syn :=
  lazymatch goal with
  | |- In ?x (?y :: _) => first [constr_eq x y; left; reflexivity | right; in_syn]
  | |- In ?x (_ ++ _) => apply in_or_app; first [left; in_syn | right; in_syn]
  | |- In ?x [] => fail
  | |- In ?x ?c => let c' := eval red in c in change (In x c'); in_syn
  end.

Section Sum.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.

Let nA : sstate * (list (sv * sv) * amode) -> jnode := nodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB.
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am.
Let Q : assn := LQP segsU LD.NP rho0 (Posts_loF_U Kc FB).

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

Hypothesis H_hl : C_CL TR Kc HFD.P0_hf S_hl.Pre_hl_U S_hl.LP.tvL_pre 299 300 S_hl.PD_hl_U.
Hypothesis H_hp : C_CL TR Kc HFD.P0_hf S_hp.Pre_hp_U S_hp.LP.tvP_pre 299 300 S_hp.PD_hp_U.
Hypothesis H_hf : C_CL TR Kc HFD.P0_hf (HFD.Pre_hf S_hf.HF_U) HFD.tv_pre 299 300 S_hf.PD_hf_U.
Hypothesis H_hvn : C_CL TR Kc S_hvn.HV.P0_hvn S_hvn.Pre_hvn_U S_hvn.HV.tv0 99 100 S_hvn.PD_hvn_U.
Hypothesis H_vr : C_CL TR Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 99 100 S_vr.PD_vr.
Hypothesis H_op : forall cm, In cm S_op.op_cms -> C_CL TR Kc S_op.OP1.P0_op (S_op.Pre_op_U cm) S_op.OP1.tv0 99 100 (S_op.PD_op_U cm).
Hypothesis H_ir : C_JA TR Kc S_ir.P0_ir S_ir.Pre_ir S_ir.tv0 S_ir.ahd NF S_ir.PDA_ir.
Hypothesis H_fs : C_JA TR Kc S_fs.P0_fs S_fs.Pre_fs S_fs.tv0 S_fs.ahd S_fs.FD.NP S_fs.PDA_fs.
Hypothesis H_mf : C_SP TR Kc rho0 FB S_mf.Pre_mf S_mf.Posts_mf.
Hypothesis H_nt : C_SP TR Kc rho0 FB S_nt.Pre_nt_U S_nt.Posts_nt_U.
Hypothesis H_si : C_SP TR Kc rho0 FB S_si.Pre_si_U S_si.Posts_si_U.
Hypothesis H_sd : C_SP TR Kc rho0 FB S_sd.Pre_sd_U S_sd.Posts_sd_U.
Hypothesis H_bw : C_SP TR Kc rho0 FB S_bw.Pre_bw S_bw.Posts_bw.
Hypothesis H_da : C_SP TR Kc rho0 FB S_da.Pre_da S_da.Posts_da.
Hypothesis H_ml : C_SP TR Kc rho0 FB S_ml.Pre_ml S_ml.Posts_ml.
Hypothesis H_se : forall lit, (exists n, In (lit, n) S_u18350.se_lits) -> C_SP TR Kc rho0 FB (S_u18350.Pre_se lit) S_u18350.Posts_se.
Hypothesis KTAIL : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_tail rho) (FAM b).
Hypothesis KBD : forall rho b, TR (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_bd rho) (FAM b).
Hypothesis REENTER : forall T tv am rv rho b,
  In (T, (tv, am), rv) LoNodes.cutsE -> 0 <= ameas (T, (tv, am), rv) rho < b -> TR (SPJ segsU (JGv tv am) T rho) (FAM b).

Lemma exits_ok_all :
  Forall (fun e => forall rho, TR (SPJ segsU (JGv (ad_tv e) (ad_am e)) (ad_state e) rho) (FAM (ameas e rho))) LoNodes.exitsE.
Proof.
  unfold LoNodes.exitsE, LoNodes.call_exits. cbn [app].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_bw.L_E_bw; first [eassumption | exact H_bw | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_bwda.L_E_bwda; first [eassumption | exact H_da | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_da0.L_E_da0; first [eassumption | exact H_da | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_da1.L_E_da1; first [eassumption | exact H_da | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_da2.L_E_da2; first [eassumption | exact H_da | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_fs.L_E_fs; first [eassumption | exact H_fs | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_hf.L_E_hf; first [eassumption | exact H_hf | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_hl.L_E_hl; first [eassumption | exact H_hl | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_hp.L_E_hp; first [eassumption | exact H_hp | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_hvn.L_E_hvn; first [eassumption | exact H_hvn | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_ir.L_E_ir; first [eassumption | exact H_ir | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_mf.L_E_mf; first [eassumption | exact H_mf | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_ml.L_E_ml; first [eassumption | exact H_ml | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_nt.L_E_nt; first [eassumption | exact H_nt | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_op1.L_E_op1; first [eassumption | exact (H_op 1 ltac:(op_cm)) | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_op3.L_E_op3; first [eassumption | exact (H_op 3 ltac:(op_cm)) | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_op3b.L_E_op3b; first [eassumption | exact (H_op 1 ltac:(op_cm)) | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA1.L_E_sdA1; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA2.L_E_sdA2; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA3.L_E_sdA3; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA4.L_E_sdA4; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA5.L_E_sdA5; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA6.L_E_sdA6; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA7.L_E_sdA7; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdA8.L_E_sdA8; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdB1.L_E_sdB1; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdB2.L_E_sdB2; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_sdB3.L_E_sdB3; first [eassumption | exact H_sd | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se1.L_E_se1; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se2.L_E_se2; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se3.L_E_se3; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se4.L_E_se4; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se5.L_E_se5; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se6.L_E_se6; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se7.L_E_se7; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se8.L_E_se8; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_se9.L_E_se9; first [eassumption | apply H_se; se_lit | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_si.L_E_si; first [eassumption | exact H_si | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_vrA.L_E_vrA; first [eassumption | exact H_vr | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho;
    eapply lo4_vrB.L_E_vrB; first [eassumption | exact H_vr | in_syn] |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KTAIL |].
  apply Forall_cons; [cbn [ad_tv ad_am ad_state fst snd]; intros rho; apply KBD |].
  apply Forall_nil.
Qed.

Lemma exits_okT : forall X tvX amX rvX rho, In ((X, (tvX, amX)), rvX) LoNodes.exitsE ->
  TR (SPJ segsU (JGv tvX amX) X rho) (FAM (ameas ((X, (tvX, amX)), rvX) rho)).
Proof.
  intros X tvX amX rvX rho Hin. exact (proj1 (Forall_forall _ _) exits_ok_all _ Hin rho).
Qed.
End SumT.

Lemma in_loop1 : In (LoFront.K_loop1, (LoU.tvL, LoU.amL), (500, LD.VLp 60 LD.z0)) LoNodes.cutsE.
Proof. left. reflexivity. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ok_sideK segsU ok Kc.
Hypothesis MC : malloc_contracts segsU C_U EC_U.
Hypothesis HFS : S_hf.handle_f_sum_stmt_U.
Hypothesis TAIL : lo_entry.K_stmt LoU.K_tail.
Hypothesis BD : lo_entry.K_stmt LoU.K_bd.

Theorem lo_loop_S : forall rho, triple segsU ok (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_loop rho) Q.
Proof.
  intros rho.
  apply (@triple_conseq segsU ok (SPJ segsU (JGv LoU.tvL LoU.amL) LoFront.K_loop1 rho) _ Q Q
           (fun w Hw => LoFront.SPJ_K_loop1 Kc FB rho0 rho w Hw) (fun w Hw => Hw)).
  refine (cfg_sound_JGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML LoNodes.FUEL LoNodes.cps LD.NP LoNodes.cutsE LoNodes.exitsE
           ok Q (proj1 HS) (ejcertA_jcertA segsU LD.NP _ _ _ _ _ ejcert_ok) _
           LoFront.K_loop1 LoU.tvL LoU.amL (500, LD.VLp 60 LD.z0) rho in_loop1).
  apply (exits_okT (triple segsU ok) (fun _ w => SPfamGJ segsU (map nA (map (@adrop) LoNodes.cutsE)) w \/ Q w)
           (triple_factsJ segsU ok) (triple_SPJ_ex segsU ok)
           (fun P P' Q' HP H => @triple_conseq segsU ok P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_soundP segsU ok) (call_soundJ segsU ok)).
  - exact (CS_hl ok Kc HS MC ML).
  - exact (CS_hp ok Kc HS MC ML).
  - exact (CS_hf HFS ok Kc HS MC ML).
  - exact (CS_hvn ok Kc HS MC ML).
  - exact (CS_vr ok Kc HS MC ML).
  - intros cm Hcm. exact (CS_op cm Hcm ok Kc HS MC ML).
  - exact (CS_ir ok Kc HS MC ML).
  - exact (CS_fs ok Kc HS MC ML).
  - exact (CS_mf ok Kc FB rho0 HS).
  - exact (CS_nt ok Kc FB rho0 HS).
  - exact (CS_si ok Kc FB rho0 HS).
  - exact (CS_sd ok Kc FB rho0 HS).
  - exact (CS_bw ok Kc FB rho0 HS).
  - exact (CS_da ok Kc FB rho0 HS).
  - exact (CS_ml ok Kc FB rho0 HS).
  - intros lit Hl. exact (CS_se lit Hl ok Kc FB rho0 HS).
  - intros rho' b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (TAIL ok Kc FB rho0 HS ML MC rho').
  - intros rho' b. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (BD ok Kc FB rho0 HS ML MC rho').
  - intros T tv am rv rho' b Hin _.
    exact (reenter_cutGAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ok LoNodes.cutsE T tv am rv Q rho' Hin).
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : malloc_contracts_ex segsU C_U EC_U.
Hypothesis HFX : S_hf.handle_f_sum_ex_stmt_U.
Hypothesis TAILX : lo_entry.K_ex_stmt LoU.K_tail.
Hypothesis BDX : lo_entry.K_ex_stmt LoU.K_bd.

Theorem lo_loop_E : forall rho, etriple segsU (SPJ segsU (JGv LoU.tvL LoU.amL) LoU.K_loop rho) Q.
Proof.
  intros rho.
  apply (@etriple_conseq segsU (SPJ segsU (JGv LoU.tvL LoU.amL) LoFront.K_loop1 rho) _ Q Q
           (fun w Hw => LoFront.SPJ_K_loop1 Kc FB rho0 rho w Hw) (fun w Hw => Hw)).
  refine (cfg_complete_JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB ML LoNodes.FUEL LoNodes.cps LD.NP LoNodes.cutsE LoNodes.exitsE
           Q ejcert_ok _ LoFront.K_loop1 LoU.tvL LoU.amL (500, LD.VLp 60 LD.z0) rho in_loop1).
  apply (exits_okT (etriple segsU) (fun b w => SPfamEJ segsU (map (enodeA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB) LoNodes.cutsE) b w \/ Q w)
           (etriple_factsJ segsU) (etriple_SPJ_ex segsU)
           (fun P P' Q' HP H => @etriple_conseq segsU P P' Q' Q' HP (fun w Hw => Hw) H)
           (call_completeP segsU) (call_completeJ segsU)).
  - exact (CE_hl Kc Hvi MCX ML).
  - exact (CE_hp Kc Hvi MCX ML).
  - exact (CE_hf HFX Kc Hvi MCX ML).
  - exact (CE_hvn Kc Hvi MCX ML).
  - exact (CE_vr Kc Hvi MCX ML).
  - intros cm Hcm. exact (CE_op cm Hcm Kc Hvi MCX ML).
  - exact (CE_ir Kc Hvi MCX ML).
  - exact (CE_fs Kc Hvi MCX ML).
  - exact (CE_mf Kc FB rho0).
  - exact (CE_nt Kc FB rho0).
  - exact (CE_si Kc FB rho0).
  - exact (CE_sd Kc FB rho0).
  - exact (CE_bw Kc FB rho0).
  - exact (CE_da Kc FB rho0).
  - exact (CE_ml Kc FB rho0).
  - intros lit Hl. exact (CE_se lit Hl Kc FB rho0).
  - intros rho' b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (TAILX Kc FB rho0 Hvi ML MCX rho').
  - intros rho' b. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | ].
    exact (BDX Kc FB rho0 Hvi ML MCX rho').
  - intros T tv am rv rho' b Hin Hm.
    apply (ereenter_cutAE segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB LoNodes.cutsE T tv am rv Q b rho' Hin). exact Hm.
Qed.
End Existence.
End Sum.

Theorem lo_loop_sum_U : S_hf.handle_f_sum_stmt_U ->
  lo_entry.K_stmt LoU.K_tail -> lo_entry.K_stmt LoU.K_bd -> lo_entry.K_stmt LoU.K_loop.
Proof.
  intros HFS TAIL BD ok Kc FB rho0 HS ML MC rho.
  exact (lo_loop_S Kc FB rho0 ML ok HS MC HFS TAIL BD rho).
Qed.

Theorem lo_loop_sum_ex_U : S_hf.handle_f_sum_ex_stmt_U ->
  lo_entry.K_ex_stmt LoU.K_tail -> lo_entry.K_ex_stmt LoU.K_bd -> lo_entry.K_ex_stmt LoU.K_loop.
Proof.
  intros HFX TAILX BDX Kc FB rho0 Hvi ML MCX rho.
  exact (lo_loop_E Kc FB rho0 ML Hvi MCX HFX TAILX BDX rho).
Qed.
