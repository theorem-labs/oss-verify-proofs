(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceAE.
Variable Lay : lib_layoutA.
Variable ar : asan_run.
Let L := lla_L Lay.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Variable LSt : lib_statics.
Variables PayOk PayExport : list byte -> Prop.

Definition lib_call_okA_x : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (sp ptr ra : Z) (payload : list byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_preA Lay ar LSt g LB FF LK cr sp ptr ra payload R M ->
    PayOk payload ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        lib_postA Lay ar LSt g' LB FF cr sp payload R M R' M' cr' ->
        PayExport payload ->
        model_rt model model' -> incl A A' -> m_halted model' = None -> MInv A' model' ->
        (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (@lib_cfgA Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfgA Lay fx R (Z_to_bv 64 (lla_entry Lay)) M model) K.

Record lib_iface_okA_x : Prop := LIOKAX {
  lioax_call : lib_call_okA_x;
  lioax_init : lib_statics_initA Lay ar LSt;
  lioax_frame : lib_statics_frameA Lay ar LSt
}.
End LibIfaceAE.

Lemma lib_call_okA_of_x : forall Lay ar scfg HI LSt (PE : list byte -> Prop),
  lib_call_okA_x Lay ar scfg HI LSt (fun _ => True) PE -> lib_call_okA Lay ar scfg HI LSt.
Proof.
  intros Lay ar scfg HI LSt PE H fx g LB FF LK cr A sp ptr ra payload R M model K PRE RI Hh MI HK CONT.
  apply (H fx g LB FF LK cr A sp ptr ra payload R M model K PRE I RI Hh MI HK).
  intros fx' g' R' M' model' cr' LK' A' POST _ MRT IA Hh' MI' LEAK RI'. exact (CONT fx' g' R' M' model' cr' LK' A' POST MRT IA Hh' MI' LEAK RI').
Qed.
Lemma lib_iface_okA_of_x : forall Lay ar scfg HI LSt (PE : list byte -> Prop),
  lib_iface_okA_x Lay ar scfg HI LSt (fun _ => True) PE -> lib_iface_okA Lay ar scfg HI LSt.
Proof.
  intros Lay ar scfg HI LSt PE [C I0 F]. constructor; [exact (lib_call_okA_of_x Lay ar scfg HI LSt PE C) | exact I0 | exact F].
Qed.

Lemma lib_call_okA_x_weaken : forall Lay ar scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_call_okA_x Lay ar scfg HI LSt P E -> lib_call_okA_x Lay ar scfg HI LSt P' E'.
Proof.
  intros Lay ar scfg HI LSt P P' E E' HP HE H fx g LB FF LK cr A sp ptr ra payload R M model K PRE OK RI Hh MI HK CONT.
  apply (H fx g LB FF LK cr A sp ptr ra payload R M model K PRE (HP _ OK) RI Hh MI HK).
  intros fx' g' R' M' model' cr' LK' A' POST EX MRT IA Hh' MI' LEAK RI'. exact (CONT fx' g' R' M' model' cr' LK' A' POST (HE _ EX) MRT IA Hh' MI' LEAK RI').
Qed.
Lemma lib_iface_okA_x_weaken : forall Lay ar scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_iface_okA_x Lay ar scfg HI LSt P E -> lib_iface_okA_x Lay ar scfg HI LSt P' E'.
Proof.
  intros Lay ar scfg HI LSt P P' E E' HP HE [C I0 F]. constructor; [exact (lib_call_okA_x_weaken Lay ar scfg HI LSt P P' E E' HP HE C) | exact I0 | exact F].
Qed.

Lemma lib_call_okA_x_of_plain : forall Lay ar scfg HI LSt (P : list byte -> Prop),
  lib_call_okA Lay ar scfg HI LSt -> lib_call_okA_x Lay ar scfg HI LSt P (fun _ => True).
Proof.
  intros Lay ar scfg HI LSt P H fx g LB FF LK cr A sp ptr ra payload R M model K PRE _ RI Hh MI HK CONT.
  apply (H fx g LB FF LK cr A sp ptr ra payload R M model K PRE RI Hh MI HK).
  intros fx' g' R' M' model' cr' LK' A' POST MRT IA Hh' MI' LEAK RI'. exact (CONT fx' g' R' M' model' cr' LK' A' POST I MRT IA Hh' MI' LEAK RI').
Qed.
