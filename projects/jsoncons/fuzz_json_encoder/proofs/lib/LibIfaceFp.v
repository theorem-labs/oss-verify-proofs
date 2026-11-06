(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg FPSteps HeapIface LibIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fp_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).
Lemma fp_ok_fx0 : fp_ok fx0.
Proof. exact fp_frm_zero_fx0. Qed.

Section LibIfaceFp.
Variable Lay : lib_layout.
Variable scfg : SpuriousCfg.
Variable HI : heap_iface.
Variable LSt : lib_statics.

Definition lib_call_ok_fp : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        fp_ok fx' ->
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs (ll_heap Lay)) scfg (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs (ll_heap Lay)) scfg (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

Record lib_iface_ok_fp : Prop := LIOKF {
  liof_call : lib_call_ok_fp;
  liof_init : lib_statics_init Lay LSt;
  liof_frame : lib_statics_frame Lay LSt
}.

(* [comment removed for export] *)
End LibIfaceFp.
