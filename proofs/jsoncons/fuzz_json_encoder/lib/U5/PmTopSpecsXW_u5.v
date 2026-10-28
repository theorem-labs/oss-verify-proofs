(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5
  PmLibSpecsW_u5 PmRef_u5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMXW.

(* [comment removed for export] *)
Definition zs_of_bytes (p : list byte) : list Z := map bv_unsigned p.
Lemma zs_of_bytes_length : forall p, length (zs_of_bytes p) = length p.
Proof. intros p. unfold zs_of_bytes. apply length_map. Qed.
Lemma zs_of_bytes_range : forall p, Forall (fun b => 0 <= b <= 255) (zs_of_bytes p).
Proof.
  intros p. unfold zs_of_bytes. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256%Z in R. lia.
Qed.

(* [comment removed for export] *)
Definition phi_lim (lim : Z) (payload : list byte) : Prop := PMR.IND (zs_of_bytes payload) < lim.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.            (* [comment removed for export] *)
Variable WD_SCR : Z.                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition read_specxw : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r Rr IS V E S2 ch gp sb bptr kx bx : Z) (rep : srep) (g : ls_state) (eg : PMES.eghost),
    let ps := PMS.ps_init sb bptr in
    cps_heap L HI PC_READ r sp (PMX.READX_SCR STRTOD_SCR WD_SCR) (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r (PMX.READX_SCR STRTOD_SCR WD_SCR) /\ a0 R Rr /\ a1 R E /\
                  PMS.reader_pre L M LBo Rr IS V E ch rep gp 0 true ps sp /\ gp = srep_data (IS + 80) rep /\
                  (forall b, In b (srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ Forall (fun b => 0 <= b <= 255) (srep_chars rep) (* [comment removed for export] *) /\
                  ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ pcredit_x L cr ps (kx + PMX.kenc L eg) bx /\
                  obj_on_stack L sp V PMES.ENC_SIZE /\ obj_on_stack L sp S2 24 /\ apart V PMES.ENC_SIZE S2 24 /\
                  apart Rr 592 V PMES.ENC_SIZE /\ apart Rr 592 S2 24 /\ apart IS 272 V PMES.ENC_SIZE /\ apart IS 272 S2 24 /\ apart V PMES.ENC_SIZE E 16 /\ apart S2 24 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state) (eg' : PMES.eghost),
          source_at M' Rr ch /\ parser_at M' (Rr + 320) ps' /\ isrc_at M' IS rep gp' rdst' /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = lb_remove ch LBo /\ pcredit_x L cr' ps' (kx + PMX.kenc L eg') bx /\ wf_ps ps' /\
          W = [(Rr, 592); (IS, 272); (E, 16); (0xdb5c0, 2); (0xfd058, 544)] ++ PMES.W_enc V S2 /\
          (* [comment removed for export] *)
          let rr := PMR.READ (srep_chars rep) in
          code = snd rr /\                                                                     (* [comment removed for export] *)
          PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (fst (fst rr)) /\
          (exists pay, 0 <= pay <= snd (fst rr) /\ PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (fst (fst rr)) + pay)).

Definition read_specxwU : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r Rr IS V E S2 ch gp sb bptr kx bx : Z) (rep : srep) (g : ls_state) (eg : PMES.eghost),
    let ps := PMS.ps_init sb bptr in
    cps_heap L HI PC_READ r sp (PMX.READX_SCR STRTOD_SCR WD_SCR) (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r (PMX.READX_SCR STRTOD_SCR WD_SCR) /\ a0 R Rr /\ a1 R E /\
                  PMS.reader_pre L M LBo Rr IS V E ch rep gp 0 true ps sp /\ gp = srep_data (IS + 80) rep /\
                  (forall b, In b (srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ Forall (fun b => 0 <= b <= 255) (srep_chars rep) /\
                  ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) /\
                  obj_on_stack L sp V PMES.ENC_SIZE /\ obj_on_stack L sp S2 24 /\ apart V PMES.ENC_SIZE S2 24 /\
                  apart Rr 592 V PMES.ENC_SIZE /\ apart Rr 592 S2 24 /\ apart IS 272 V PMES.ENC_SIZE /\ apart IS 272 S2 24 /\ apart V PMES.ENC_SIZE E 16 /\ apart S2 24 E 16 /\
                  PMW.wroomU eg (PMR.K (srep_chars rep)) (PMR.ALLOW (srep_chars rep)))
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state) (eg' : PMES.eghost),
          source_at M' Rr ch /\ parser_at M' (Rr + 320) ps' /\ isrc_at M' IS rep gp' rdst' /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = lb_remove ch LBo /\ pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') /\ wf_ps ps' /\
          W = [(Rr, 592); (IS, 272); (E, 16); (0xdb5c0, 2); (0xfd058, 544)] ++ PMES.W_enc V S2 /\
          let rr := PMR.READ (srep_chars rep) in
          code = snd rr /\
          PMES.g_es eg' = PMW.es_run (PMES.g_es eg) (fst (fst rr)) /\
          (exists pay, 0 <= pay <= snd (fst rr) /\ PMES.g_len eg' = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (fst (fst rr)) + pay)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lib_call_ok_fpw (PHI : list byte -> Prop) (Lay : lib_layout) (LSt : lib_statics) : Prop :=
  forall (fx : FPState) (g : LibIface.ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : LibIface.ls_state LSt) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
        fp_ok fx' ->
        PHI payload ->
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs (ll_heap Lay)) SCFG (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs (ll_heap Lay)) SCFG (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

(* [comment removed for export] *)
Definition lib_specxw (PHI : list byte -> Prop) (Lay : lib_layout) : Prop :=
  PMX.pm_layout_okx L STRTOD_SCR WD_SCR Lay -> lib_call_ok_fpw PHI Lay PMX.pm_staticsx.

(* [comment removed for export] *)
Lemma lib_specx_of_w : forall PHI Lay, lib_specxw PHI Lay -> PMX.lib_specx L HI STRTOD_SCR WD_SCR Lay.
Proof.
  intros PHI Lay W HL fx g LB cr sp ptr ra payload R M model K HFP HPRE HH Hh Hlz Hmt HK CONT.
  apply (W HL fx g LB cr sp ptr ra payload R M model K HFP HPRE HH Hh Hlz Hmt HK).
  intros fx' g' R' M' model' cr' HFP' _ HPOST HH' HBUT. exact (CONT fx' g' R' M' model' cr' HFP' HPOST HH' HBUT).
Qed.
End Specs.

(* [comment removed for export] *)
Lemma phi_lim_of_len : forall lim payload es0 len0 pay len cap_bound,
  PMR.IND (zs_of_bytes payload) = PMW.ind_run [] (PMR.K (zs_of_bytes payload)) ->
  es0 = [] -> len0 = 0 -> 0 <= pay ->
  len = len0 + PMW.ind_run es0 (PMR.K (zs_of_bytes payload)) + pay ->
  len < cap_bound -> cap_bound <= lim ->
  phi_lim lim payload.
Proof. intros lim payload es0 len0 pay len cb HIND -> -> Hpay Hlen Hlt Hle. unfold phi_lim. rewrite HIND. lia. Qed.

End PMXW.
