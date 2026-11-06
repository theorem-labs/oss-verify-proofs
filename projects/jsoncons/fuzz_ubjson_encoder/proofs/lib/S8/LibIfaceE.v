(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceE.
Variable Lay : lib_layout.
Let L := ll_heap Lay.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.
Variable LSt : lib_statics.
Variables PayOk PayExport : list byte -> Prop.

Definition lib_call_ok_x : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    PayOk payload ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        PayExport payload ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs L) scfg (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

Record lib_iface_ok_x : Prop := LIOKX {
  liox_call : lib_call_ok_x;
  liox_init : lib_statics_init Lay LSt;
  liox_frame : lib_statics_frame Lay LSt
}.
End LibIfaceE.

Lemma lib_call_ok_of_x {bmK : BMode} : forall Lay scfg HI LSt (PE : list byte -> Prop),
  lib_call_ok_x Lay scfg HI LSt (fun _ => True) PE -> lib_call_ok Lay scfg HI LSt.
Proof.
  intros Lay scfg HI LSt PE H fx g LB cr sp ptr ra payload R M model K PRE HH Hh Hl Hm HK CONT.
  apply (H fx g LB cr sp ptr ra payload R M model K PRE I HH Hh Hl Hm HK).
  intros fx' g' R' M' model' cr' POST _ HH' HB. exact (CONT fx' g' R' M' model' cr' POST HH' HB).
Qed.
Lemma lib_iface_ok_of_x {bmK : BMode} : forall Lay scfg HI LSt (PE : list byte -> Prop),
  lib_iface_ok_x Lay scfg HI LSt (fun _ => True) PE -> lib_iface_ok Lay scfg HI LSt.
Proof.
  intros Lay scfg HI LSt PE [C I0 F]. constructor; [exact (lib_call_ok_of_x Lay scfg HI LSt PE C) | exact I0 | exact F].
Qed.

Lemma lib_call_ok_x_weaken {bmK : BMode} : forall Lay scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_call_ok_x Lay scfg HI LSt P E -> lib_call_ok_x Lay scfg HI LSt P' E'.
Proof.
  intros Lay scfg HI LSt P P' E E' HP HE H fx g LB cr sp ptr ra payload R M model K PRE OK HH Hh Hl Hm HK CONT.
  apply (H fx g LB cr sp ptr ra payload R M model K PRE (HP _ OK) HH Hh Hl Hm HK).
  intros fx' g' R' M' model' cr' POST EX HH' HB. exact (CONT fx' g' R' M' model' cr' POST (HE _ EX) HH' HB).
Qed.
