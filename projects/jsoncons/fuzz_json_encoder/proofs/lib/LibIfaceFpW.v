(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg FPSteps HeapIface LibIface LibIfaceFp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceFpW.
Variable Lay : lib_layout.
Variable scfg : SpuriousCfg.
Variable HI : heap_iface.
Variable LSt : lib_statics.
Variable PHI : list byte -> Prop.

Definition lib_call_ok_fpw : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        fp_ok fx' ->
        PHI payload ->
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs (ll_heap Lay)) scfg (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs (ll_heap Lay)) scfg (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

Record lib_iface_ok_fpw : Prop := LIOKFW {
  liofw_call : lib_call_ok_fpw;
  liofw_init : lib_statics_init Lay LSt;
  liofw_frame : lib_statics_frame Lay LSt
}.

Lemma lib_call_ok_fp_of_w : lib_call_ok_fpw -> lib_call_ok_fp Lay scfg HI LSt.
Proof.
  intros W fx g LB cr sp ptr ra payload R M model K HFP HPRE HH Hh Hlz Hmt HK CONT.
  apply (W fx g LB cr sp ptr ra payload R M model K HFP HPRE HH Hh Hlz Hmt HK).
  intros fx' g' R' M' model' cr' HFP' _ HPOST HH' HBUT. exact (CONT fx' g' R' M' model' cr' HFP' HPOST HH' HBUT).
Qed.

Lemma lib_iface_ok_fp_of_w : lib_iface_ok_fpw -> lib_iface_ok_fp Lay scfg HI LSt.
Proof. intros [C I F]. split; [exact (lib_call_ok_fp_of_w C) | exact I | exact F]. Qed.
End LibIfaceFpW.
