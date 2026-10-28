(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The library top of the ubsan target at vm_limit 2^39 (twin of PmTopSpecsXW.lib_specxw and HarnessXW.lib_ok_xw).
   - pm_layout_okxU: PMX.pm_layout_okx with the library credit of the ubsan contract (LCU.lay_creditU).
   - lib_specxU: on such a layout the library call satisfies LCU.lib_call_okU, the contract that consumes PHI.
   - harness_runU: the statement of the harness run (twin of HNXW.run_ok): the plain one with the credit
     LCU.pm_creditxU, the payload bound IND < 2^34 as a premise (the harness gives read its output room from it),
     and a continuation that no longer has to produce PHI.
   - lib_specxU_of_run: the composition, from harness_runU and LCU.phiwU PHI. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PmRef.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopSpecs_u5 TopKit2_u5 TopKitX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LSU.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable SS : Z.     (* strtod scratch of the library layout (PML.STRTOD_SCR_V) *)
Variable WD : Z.     (* double-writer scratch (PMES.WD_SCR_X) *)

Definition pm_layout_okxU (Lay : lib_layout) : Prop :=
  ll_heap Lay = L /\ ll_entry Lay = PML.PC_LIB /\ ll_gp Lay = 0x10800 /\ PMX.LIB_SCRX SS WD <= ll_stack Lay /\
  ll_foot Lay = PML.ll_footx_xsrc /\ LCU.lay_creditU L Lay /\ PML.IMG_RO_HI <= ll_rw_lo Lay.

Definition lib_specxU (PHI : list byte -> Prop) (Lay : lib_layout) : Prop :=
  pm_layout_okxU Lay -> LCU.lib_call_okU Lay SCFG HI PMX.pm_staticsx PHI.

Definition harness_runU : Prop :=
  forall (Lay : lib_layout),
    ll_heap Lay = L -> ll_foot Lay = PML.ll_footx_xsrc -> LCU.lay_creditU L Lay ->
    1376 + 9568 <= ll_stack Lay -> 1376 + PMX.READX_SCR SS WD <= ll_stack Lay ->
  forall (LB : list (Z * Z)) (cr : credit) (sp ra : Z) (payload : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : ShapeAlg.TSet),
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 PML.TP ->
    0 <= Z.of_nat (length payload) < 2 ^ 26 -> L5.ra_ok ra ->
    (2 ^ 40 <= sp <= 2 ^ 47 /\ sp mod 16 = 0) ->
    hl_ceil L + ll_stack Lay <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
    TK2.blocks_ok L LB -> K [] ->
    PmRef.PMR.IND (map bv_unsigned payload) < 2 ^ 34 ->
    (forall (fx' : FPState) (g' : PML.ls_state) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        PML.fp_ok fx' -> lib_post Lay PMX.pm_staticsx g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model model' ->
        srealizes PML.RSEGS SCFG (@PML.cfg fx' R' ra M' model') K) ->
  forall (fx : FPState) (g : PML.ls_state) (ptr : Z),
    PML.fp_ok fx -> getr R 1%bv = Z_to_bv 64 ra -> getr R 10%bv = Z_to_bv 64 ptr ->
    getr R 11%bv = Z_to_bv 64 (Z.of_nat (length payload)) ->
    ((length payload = 0%nat) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn PML.RSEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (LCU.pm_creditxU L (Z.of_nat (length payload))) cr -> PML.ls_ok g M -> PML.lits_ok M ->
    hi_heap HI LB cr M (m_vmmaps model) -> PML.model_ok model ->
    (forall a, sp - ll_stack Lay <= a < sp -> M (Z_to_bv 64 a) <> None) ->
    srealizes PML.RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K.

(* The library functions the harness calls, at their U specs (reader with output room and byte credit). *)
Record lib_fnspecsU : Prop := LFSU {
  lfs_strinit : PMS.strinit_spec L HI;
  lfs_iss : PMS.iss_ctor_spec L HI;
  lfs_enc_ctor : PMES.enc_ctor_spec L HI;
  lfs_rctor : PMS.reader_ctor_spec L HI;
  lfs_syscat : PMS.system_category_spec L;
  lfs_read : PMXW.read_specxwU L HI SS WD;
  lfs_pdtor : PMS.parser_dtor_spec L HI;
  lfs_sdtor : PMS.source_dtor_spec L HI;
  lfs_enc_dtor : PMES.enc_dtor_spec L HI;
  lfs_opdels : PMS.opdel_sized_spec L HI;
  lfs_locdtor : PMS.locale_dtor_spec L;
  lfs_istrdtor : TPS.istream_dtor_spec L;
  lfs_iosbdtor : TPS.iosb_dtor_spec L
}.

Definition fp_inv : Prop := forall (fx fx' : FPState) R pc M R' pc' M',
  msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) ->
  PML.fp_ok fx -> PML.fp_ok fx'.

Lemma stack_bounds : forall Lay, PMX.LIB_SCRX SS WD <= ll_stack Lay ->
  1376 + 9568 <= ll_stack Lay /\ 1376 + PMX.READX_SCR SS WD <= ll_stack Lay.
Proof.
  intros Lay H. unfold PMX.LIB_SCRX in H.
  assert (E : PMS.RCTOR_SCR = 9568) by (vm_compute; reflexivity).
  pose proof (Z.le_max_l (PMX.READX_SCR SS WD) (Z.max (Z.max PMS.RCTOR_SCR PMS.ISS_SCR) PMES.ENC_CTOR_SCR)) as M1.
  pose proof (Z.le_max_r (PMX.READX_SCR SS WD) (Z.max (Z.max PMS.RCTOR_SCR PMS.ISS_SCR) PMES.ENC_CTOR_SCR)) as M2.
  pose proof (Z.le_max_l (Z.max PMS.RCTOR_SCR PMS.ISS_SCR) PMES.ENC_CTOR_SCR) as M3.
  pose proof (Z.le_max_l PMS.RCTOR_SCR PMS.ISS_SCR) as M4.
  lia.
Qed.

Section Compose.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis RUN : harness_runU.

Theorem lib_specxU_of_run : forall PHI, LCU.phiwU PHI -> forall Lay, lib_specxU PHI Lay.
Proof.
  intros PHI PHIW Lay LOK. destruct LOK as (HL & HEN & _ & HSTK & HFT & HCR & _).
  destruct (stack_bounds Lay HSTK) as [HSS HSSR].
  unfold LCU.lib_call_okU. intros fx g LB cr sp ptr ra payload R M model K Hfp HPHI PRE HH Hh Hlz Hmt HK CONT.
  pose proof (lib_pre_floor Lay PMX.pm_staticsx g LB cr sp ptr ra payload R M PRE) as FLOOR.
  destruct PRE as [Pra Prok Psp Pgp Ptp Pa0 Pa1 Plen Pptr Ppay Pstk Pcr Pst].
  pose proof (PmLayout.ly_segs L LAY) as HSEG. pose proof (PmLayout.ly_tp L LAY) as HTP.
  unfold lib_cfg in CONT |- *. rewrite HEN. rewrite HL in *. rewrite HSEG in *. rewrite HTP in Ptp.
  destruct Pstk as (S1 & S2 & S3 & S4 & S5 & S6).
  unfold LCU.lay_creditU in HCR. rewrite HCR in Pcr.
  cbn [LibIface.ls_ok PMX.pm_staticsx] in Pst. unfold PML.ls_okx in Pst. destruct Pst as [Pls Plit].
  change (srealizes PML.RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K).
  refine (RUN Lay HL HFT HCR HSS HSSR LB cr sp ra payload R M model K Psp Ptp _ Prok _ S2 S3 S4 _ HK (PHIW payload HPHI) _
            fx g ptr Hfp Pra Pa0 Pa1 _ Ppay Pcr Pls _ HH (conj Hh (conj Hlz Hmt)) S6).
  - lia.
  - split; [lia | exact S1].
  - eapply TK2.blocks_ok_heap; eauto.
  - intros fx' g' R' M' model' cr' F1 F2 F3 F4. exact (CONT fx' g' R' M' model' cr' F1 F2 F3 F4).
  - destruct Pptr as [(P0 & _) | P1]; [left; exact P0 | right; exact P1].
  - destruct g; try exact Plit. apply TKX.lits_pristine_ok. exact Plit.
Qed.
End Compose.
End Specs.
End LSU.
