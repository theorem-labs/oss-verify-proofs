(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require FPSteps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceAW.
Variable Lay : lib_layoutA.
Variable ar : asan_run.
Let L := lla_L Lay.
Let LV := lib_view Lay ar.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Variable LSt : lib_statics.
Variable PHI : list byte -> Prop.

Definition lib_call_okAW : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (sp ptr ra : Z) (payload : list byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->                                                                                                       (* [comment removed for export] *)
    PHI payload ->                                                                                                    (* [comment removed for export] *)
    lib_preA Lay ar LSt g LB FF LK cr sp ptr ra payload R M ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        fp_ok fx' ->                                                                                                  (* [comment removed for export] *)
        lib_postA Lay ar LSt g' LB FF cr sp payload R M R' M' cr' ->
        model_rt model model' -> incl A A' -> m_halted model' = None -> MInv A' model' ->
        (forall k, In k PM_FS_CLASSES -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->      (* [comment removed for export] *)
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (@lib_cfgA Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfgA Lay fx R (Z_to_bv 64 (lla_entry Lay)) M model) K.

(* [comment removed for export] *)


Record lib_iface_okAW (ls_atexit : ls_state LSt -> list (Z * Z)) : Prop := LIOKAW {
  lioaw_call : lib_call_okAW;
  lioaw_init : lib_statics_initA Lay ar LSt;
  lioaw_frame : lib_statics_frameA Lay ar LSt;
  lioaw_exit : lib_exit_factsA Lay LSt ls_atexit
}.

Lemma lib_call_okAW_of_plain : lib_call_okA Lay ar scfg HI LSt -> lib_call_okAW.
Proof.
  intros C fx g LB FF LK cr A sp ptr ra payload R M model K HFP _ HPRE HRI Hh HMI HK CONT.
  exact (C fx g LB FF LK cr A sp ptr ra payload R M model K HFP HPRE HRI Hh HMI HK CONT).
Qed.
Lemma lib_iface_okAW_of_plain : forall lsa, lib_iface_okA Lay ar scfg HI LSt lsa -> lib_iface_okAW lsa.
Proof. intros lsa [C I F X]. split; [exact (lib_call_okAW_of_plain C) | exact I | exact F | exact X]. Qed.
End LibIfaceAW.
