From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require S_hl S_hp hl hp fsB vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require S_hf S_bw bw.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require S_hvn S_op S_u18350 hvn op fs fsT u18350.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L14 Require S_ir ir.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_fs S_ml ml vf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_da vr da aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require S_mf mf pc.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10 Require S_nt S_si S_sd nt si sd.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1 Lib_handle__G1.
Import ListNotations.
Open Scope Z_scope.

Module LG := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue.
Module HFD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.

(* The callee hypotheses C_x of the lo call-site files U/L1/lo4_<x>.v, as definitions over the transformer TR
   (triple segsU ok for safety, etriple segsU for existence). C_x in lo4_<x>.v is convertible to the C_* below at
   the callee's arguments. *)

(* client callee with a JG summary, called with the arena-head mode AHead (SVar h) (P's JGA_frame_sum form) *)
Definition C_CL (TR : assn -> assn -> Prop) (Kc : list event -> Model -> Prop) (P0c : list (Z * Z) -> valuation -> Prop)
    (Pre : sstate) (tv : list (sv * sv)) (h NP : positive) (PD : list (sstate * list (sv * sv))) : Prop :=
  forall FBc rho1, TR (SPJ segsU (JGA_pre segsU C_U Kc (P0c FBc) FBc tv (AHead (SVar h))) Pre rho1)
                      (LQP segsU NP rho1 (PostsCA segsU C_U Kc P0c (PDAh PD h) FBc)).

(* client callee whose summary is already in JGA form *)
Definition C_JA (TR : assn -> assn -> Prop) (Kc : list event -> Model -> Prop) (P0c : list (Z * Z) -> valuation -> Prop)
    (Pre : sstate) (tv : list (sv * sv)) (am : amode) (NP : positive) (PDA : list (sstate * (list (sv * sv) * amode))) : Prop :=
  forall FBc rho1, TR (SPJ segsU (JGA_pre segsU C_U Kc (P0c FBc) FBc tv am) Pre rho1)
                      (LQP segsU NP rho1 (PostsCA segsU C_U Kc P0c PDA FBc)).

(* pure callee with an SP / LQ summary, framed by lo's invariant *)
Definition C_SP (TR : assn -> assn -> Prop) (Kc : list event -> Model -> Prop) (rho0 : valuation) (FB : list (Z * Z))
    (Pre : sstate) (Posts : list leaf) : Prop :=
  forall tv am rho rho1,
    TR (SP segsU (fun tr md => JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am rho tr md) Pre rho1)
       (LQ segsU (fun tr md => JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tv am rho tr md) (ss_next Pre) rho1 Posts).

Lemma sp_S : forall (Pre : sstate) (Posts : list leaf), ss_next Pre = NF ->
  (forall ok K rho, ok_frame segsU ok K -> triple segsU ok (SP segsU K Pre rho) (LQ segsU K NF rho Posts)) ->
  forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB Pre Posts.
Proof.
  intros Pre Posts Hn H ok Kc FB rho0 HS tv am rho rho1. rewrite Hn. apply H.
  eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
Qed.

Lemma sp_E : forall (Pre : sstate) (Posts : list leaf), ss_next Pre = NF ->
  (forall K rho, etriple segsU (SP segsU K Pre rho) (LQ segsU K NF rho Posts)) ->
  forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB Pre Posts.
Proof. intros Pre Posts Hn H Kc FB rho0 tv am rho rho1. rewrite Hn. apply H. Qed.

Section Callees.
(* handle_f's summary is not closed on the hub yet (t-L5's assembly U/L5/hf_asm.v only has handle_f_sum_gen). *)
Hypothesis HFS : S_hf.handle_f_sum_stmt_U.
Hypothesis HFX : S_hf.handle_f_sum_ex_stmt_U.

(* ---- client callees, safety ---- *)
Lemma CS_hl : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc HFD.P0_hf S_hl.Pre_hl_U S_hl.LP.tvL_pre 299 300 S_hl.PD_hl_U.
Proof.
  intros ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc HFD.P0_hf S_hl.Pre_hl_U S_hl.LP.tvL_pre S_hl.PD_hl_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) ok (fun FBc rho1 => hl.handle_l_sum_U pc.parse_corner_sum_U da.da_sum vr.vr_sum ok Kc FBc rho1 HS MC ML)).
Qed.

Lemma CS_hp : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc HFD.P0_hf S_hp.Pre_hp_U S_hp.LP.tvP_pre 299 300 S_hp.PD_hp_U.
Proof.
  intros ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc HFD.P0_hf S_hp.Pre_hp_U S_hp.LP.tvP_pre S_hp.PD_hp_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) ok (fun FBc rho1 => hp.handle_p_sum_U pc.parse_corner_sum_U da.da_sum vr.vr_sum ok Kc FBc rho1 HS MC ML)).
Qed.

Lemma CS_hf : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc HFD.P0_hf (HFD.Pre_hf S_hf.HF_U) HFD.tv_pre 299 300 S_hf.PD_hf_U.
Proof.
  intros ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc HFD.P0_hf (HFD.Pre_hf S_hf.HF_U) HFD.tv_pre S_hf.PD_hf_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) ok (fun FBc rho1 => HFS ok Kc FBc rho1 HS MC ML)).
Qed.

Lemma CS_hvn : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc S_hvn.HV.P0_hvn S_hvn.Pre_hvn_U S_hvn.HV.tv0 99 100 S_hvn.PD_hvn_U.
Proof.
  intros ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc S_hvn.HV.P0_hvn S_hvn.Pre_hvn_U S_hvn.HV.tv0 S_hvn.PD_hvn_U 100 99 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) ok (fun FBc rho1 => hvn.handle_vn_sum_U sd.scan_double_sum_U vr.vr_sum ok Kc FBc rho1 HS ML MC)).
Qed.

Lemma CS_vr : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 99 100 S_vr.PD_vr.
Proof.
  intros ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 S_vr.PD_vr 100 99 ML eq_refl (fun F F' r _ H => H) ok (fun FBc rho1 => vr.vr_sum ok Kc FBc rho1 HS ML MC)).
Qed.

Lemma CS_op : forall cm, In cm S_op.op_cms -> forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (triple segsU ok) Kc S_op.OP1.P0_op (S_op.Pre_op_U cm) S_op.OP1.tv0 99 100 (S_op.PD_op_U cm).
Proof.
  intros cm Hcm ok Kc HS MC ML. exact (JGA_frame_sum segsU C_U Kc S_op.OP1.P0_op (S_op.Pre_op_U cm) S_op.OP1.tv0 (S_op.PD_op_U cm) 100 99 ML eq_refl (fun F F' r _ H => H) ok (fun FBc rho1 => op.opt_push_sum_U vr.vr_sum cm Hcm ok Kc FBc rho1 HS ML MC)).
Qed.

Lemma CS_ir : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_JA (triple segsU ok) Kc S_ir.P0_ir S_ir.Pre_ir S_ir.tv0 S_ir.ahd NF S_ir.PDA_ir.
Proof. intros ok Kc HS MC ML FBc rho1. exact (ir.intern_rest_sum_U aa.aa_sum ok Kc FBc rho1 HS ML MC). Qed.

Lemma CS_fs : forall ok Kc, ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_JA (triple segsU ok) Kc S_fs.P0_fs S_fs.Pre_fs S_fs.tv0 S_fs.ahd S_fs.FD.NP S_fs.PDA_fs.
Proof.
  intros ok Kc HS MC ML FBc rho1.
  exact (fs.fs_sum_U aa.aa_sum (fsB.fsB_sum_U (vf.vf_sum_U aa.aa_sum) (fsT.fsT_sum_U vp.vp_sum)) ok Kc FBc rho1 HS ML MC).
Qed.

(* ---- client callees, existence ---- *)
Lemma CE_hl : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc HFD.P0_hf S_hl.Pre_hl_U S_hl.LP.tvL_pre 299 300 S_hl.PD_hl_U.
Proof.
  intros Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc HFD.P0_hf S_hl.Pre_hl_U S_hl.LP.tvL_pre S_hl.PD_hl_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) (fun FBc rho1 => ltac:(apply (hl.handle_l_sum_ex_U pc.parse_corner_sum_ex_U da.da_sum_ex vr.vr_sum_ex); assumption))).
Qed.

Lemma CE_hp : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc HFD.P0_hf S_hp.Pre_hp_U S_hp.LP.tvP_pre 299 300 S_hp.PD_hp_U.
Proof.
  intros Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc HFD.P0_hf S_hp.Pre_hp_U S_hp.LP.tvP_pre S_hp.PD_hp_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) (fun FBc rho1 => ltac:(apply (hp.handle_p_sum_ex_U pc.parse_corner_sum_ex_U da.da_sum_ex vr.vr_sum_ex); assumption))).
Qed.

Lemma CE_hf : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc HFD.P0_hf (HFD.Pre_hf S_hf.HF_U) HFD.tv_pre 299 300 S_hf.PD_hf_U.
Proof.
  intros Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc HFD.P0_hf (HFD.Pre_hf S_hf.HF_U) HFD.tv_pre S_hf.PD_hf_U 300 299 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) (fun FBc rho1 => ltac:(apply HFX; assumption))).
Qed.

Lemma CE_hvn : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc S_hvn.HV.P0_hvn S_hvn.Pre_hvn_U S_hvn.HV.tv0 99 100 S_hvn.PD_hvn_U.
Proof.
  intros Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc S_hvn.HV.P0_hvn S_hvn.Pre_hvn_U S_hvn.HV.tv0 S_hvn.PD_hvn_U 100 99 ML eq_refl (fun F F' r Hs H => LG.P0txt_mono _ _ F F' r Hs H) (fun FBc rho1 => ltac:(apply (hvn.handle_vn_sum_ex_U sd.scan_double_sum_ex_U vr.vr_sum_ex); assumption))).
Qed.

Lemma CE_vr : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 99 100 S_vr.PD_vr.
Proof.
  intros Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc (fun _ : list (Z * Z) => S_vr.P0_vr) S_vr.Pre_vr S_vr.tv0 S_vr.PD_vr 100 99 ML eq_refl (fun F F' r _ H => H) (fun FBc rho1 => ltac:(apply vr.vr_sum_ex; assumption))).
Qed.

Lemma CE_op : forall cm, In cm S_op.op_cms -> forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_CL (etriple segsU) Kc S_op.OP1.P0_op (S_op.Pre_op_U cm) S_op.OP1.tv0 99 100 (S_op.PD_op_U cm).
Proof.
  intros cm Hcm Kc Hvi MCX ML. exact (JGA_frame_sum_ex segsU C_U Kc S_op.OP1.P0_op (S_op.Pre_op_U cm) S_op.OP1.tv0 (S_op.PD_op_U cm) 100 99 ML eq_refl (fun F F' r _ H => H) (fun FBc rho1 => ltac:(apply (op.opt_push_sum_ex_U vr.vr_sum_ex cm Hcm); assumption))).
Qed.

Lemma CE_ir : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_JA (etriple segsU) Kc S_ir.P0_ir S_ir.Pre_ir S_ir.tv0 S_ir.ahd NF S_ir.PDA_ir.
Proof. intros Kc Hvi MCX ML FBc rho1. apply (ir.intern_rest_ex_U aa.aa_sum_ex); assumption. Qed.

Lemma CE_fs : forall Kc, vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
  C_JA (etriple segsU) Kc S_fs.P0_fs S_fs.Pre_fs S_fs.tv0 S_fs.ahd S_fs.FD.NP S_fs.PDA_fs.
Proof.
  intros Kc Hvi MCX ML FBc rho1.
  apply (fs.fs_ex_U aa.aa_sum_ex (fsB.fsB_ex_U (vf.vf_ex_U aa.aa_sum_ex) (fsT.fsT_ex_U vp.vp_sum_ex))); assumption.
Qed.
End Callees.

(* ---- pure callees (SP summaries), safety and existence ---- *)
Lemma CS_mf : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_mf.Pre_mf S_mf.Posts_mf.
Proof. exact (sp_S S_mf.Pre_mf S_mf.Posts_mf eq_refl mf.mat_find_sum_U). Qed.
Lemma CE_mf : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_mf.Pre_mf S_mf.Posts_mf.
Proof. exact (sp_E S_mf.Pre_mf S_mf.Posts_mf eq_refl mf.mat_find_sum_ex_U). Qed.

Lemma CS_nt : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_nt.Pre_nt_U S_nt.Posts_nt_U.
Proof. exact (sp_S S_nt.Pre_nt_U S_nt.Posts_nt_U eq_refl nt.next_token_sum_U). Qed.
Lemma CE_nt : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_nt.Pre_nt_U S_nt.Posts_nt_U.
Proof. exact (sp_E S_nt.Pre_nt_U S_nt.Posts_nt_U eq_refl nt.next_token_sum_ex_U). Qed.

Lemma CS_si : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_si.Pre_si_U S_si.Posts_si_U.
Proof. exact (sp_S S_si.Pre_si_U S_si.Posts_si_U eq_refl si.scan_int_sum_U). Qed.
Lemma CE_si : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_si.Pre_si_U S_si.Posts_si_U.
Proof. exact (sp_E S_si.Pre_si_U S_si.Posts_si_U eq_refl si.scan_int_sum_ex_U). Qed.

Lemma CS_sd : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_sd.Pre_sd_U S_sd.Posts_sd_U.
Proof. exact (sp_S S_sd.Pre_sd_U S_sd.Posts_sd_U eq_refl sd.scan_double_sum_U). Qed.
Lemma CE_sd : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_sd.Pre_sd_U S_sd.Posts_sd_U.
Proof. exact (sp_E S_sd.Pre_sd_U S_sd.Posts_sd_U eq_refl sd.scan_double_sum_ex_U). Qed.

Lemma CS_bw : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_bw.Pre_bw S_bw.Posts_bw.
Proof. exact (sp_S S_bw.Pre_bw S_bw.Posts_bw eq_refl bw.bw_sum). Qed.
Lemma CE_bw : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_bw.Pre_bw S_bw.Posts_bw.
Proof. exact (sp_E S_bw.Pre_bw S_bw.Posts_bw eq_refl bw.bw_sum_ex). Qed.

Lemma CS_da : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_da.Pre_da S_da.Posts_da.
Proof. exact (sp_S S_da.Pre_da S_da.Posts_da eq_refl da.da_sum). Qed.
Lemma CE_da : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_da.Pre_da S_da.Posts_da.
Proof. exact (sp_E S_da.Pre_da S_da.Posts_da eq_refl da.da_sum_ex). Qed.

Lemma CS_ml : forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB S_ml.Pre_ml S_ml.Posts_ml.
Proof. exact (sp_S S_ml.Pre_ml S_ml.Posts_ml eq_refl ml.ml_sum). Qed.
Lemma CE_ml : forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB S_ml.Pre_ml S_ml.Posts_ml.
Proof. exact (sp_E S_ml.Pre_ml S_ml.Posts_ml eq_refl ml.ml_sum_ex). Qed.

(* slice_eq: one summary per literal of the dispatch table S_u18350.se_lits *)
Lemma CS_se : forall lit, (exists n, In (lit, n) S_u18350.se_lits) ->
  forall ok Kc FB rho0, ok_sideK segsU ok Kc -> C_SP (triple segsU ok) Kc rho0 FB (S_u18350.Pre_se lit) S_u18350.Posts_se.
Proof. intros lit [n Hin]. exact (sp_S (S_u18350.Pre_se lit) S_u18350.Posts_se eq_refl (u18350.slice_eq_sum lit n Hin)). Qed.
Lemma CE_se : forall lit, (exists n, In (lit, n) S_u18350.se_lits) ->
  forall Kc FB rho0, C_SP (etriple segsU) Kc rho0 FB (S_u18350.Pre_se lit) S_u18350.Posts_se.
Proof. intros lit [n Hin]. exact (sp_E (S_u18350.Pre_se lit) S_u18350.Posts_se eq_refl (u18350.slice_eq_sum_ex lit n Hin)). Qed.

(* membership side conditions of the slice_eq and opt_push instances *)
Ltac se_lit := eexists; cbn; repeat (first [left; reflexivity | right]).
Ltac op_cm := cbn; tauto.
