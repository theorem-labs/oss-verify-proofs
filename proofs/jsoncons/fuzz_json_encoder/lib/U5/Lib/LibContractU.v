(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The library contract of the ubsan target at vm_limit 2^39.
   The plain library pays big allocations with a call count only and produces PHI (PMXW.lib_call_ok_fpw). At 2^39 no
   budget refusal is absorbed, so this contract
   - consumes PHI as a premise (lib_call_okU, the direction of PmLibIfaceAW.lib_call_okAW),
   - pays every allocation in bytes: the library's initial credit carries the encoder's byte potential PMES.benc of the
     U specs (U5/PmEncSpecs_u5.v) next to its call-count potential PMES.kenc,
   - bounds the output by the room PMES.CLU >= IND + ALLOW (clok_CLU), IND from PHI (phiwU). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare HeapIface LibIface LibIfaceFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PmRef PmRefAllow.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmLibDefs_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LCU.
Module PMES := PmEncSpecs_u5.PMES.

(* The payload predicate of the statement bounds the plain reference model's output: IND < 2^34 (PHI0U). *)
Definition phiwU (PHI : list byte -> Prop) : Prop :=
  forall payload : list byte, PHI payload -> PmRef.PMR.IND (map bv_unsigned payload) < 2 ^ 34.

(* The room CLU covers IND + ALLOW of every payload of PHI0U (ALLOW p <= 32 * |p| + 32, |p| < 2^26). *)
Lemma clok_CLU : forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> PmRef.PMR.IND txt < 2 ^ 34 ->
  PmRef.PMR.IND txt + PmRef.PMR.ALLOW txt <= PMES.CLU.
Proof. intros txt Hn HI. pose proof (PmRefAllow.PMRA.ALLOW_bound txt). unfold PMES.CLU. lia. Qed.

Section Credit.
Variable L : heap_layout.

(* Initial credit of one library call on an input of n bytes: the plain PMX.pm_creditx plus the encoder's bytes. *)
Definition pm_creditxU (n : Z) : credit :=
  (28 * hl_k_per_malloc L + PMES.kenc L PMES.g0, 2 * n + 2 ^ 28 + 32768 + 28 * hl_b_overhead L + PMES.benc L PMES.g0).

Lemma kenc_g0 : PMES.kenc L PMES.g0 = 54 * hl_k_per_malloc L.
Proof.
  unfold PMES.kenc, PMES.g0. cbn [PMES.g_rep PMES.g_scap].
  assert (E1 : PMES.kv_s2 (PmLibDefs_u5.PML.SShort []) = 43) by reflexivity.
  assert (E2 : PMES.kv_st 0 = 11) by reflexivity.
  rewrite E1, E2. lia.
Qed.

Lemma benc_g0 : PMES.benc L PMES.g0 = 4 * PMES.CLU + 65506 + 54 * hl_b_overhead L.
Proof.
  unfold PMES.benc, PMES.bpot_s2, PMES.bpot_st, PMES.g0. cbn [PMES.g_rep PMES.g_scap].
  assert (E1 : PMES.kv_s2 (PmLibDefs_u5.PML.SShort []) = 43) by reflexivity.
  assert (E2 : PMES.kv_st 0 = 11) by reflexivity.
  assert (E3 : PMES.alloc_of (PmLibDefs_u5.PML.SShort []) = 23) by reflexivity.
  rewrite E1, E2, E3. unfold PMES.CLU. lia.
Qed.
End Credit.

(* The library credit of one call fits the ubsan heap's initial credit (K0U, B0U) under the driver reserve of
   Pm6DrvMainW.v:167-169 (4 library credits plus the input) and Pm6DrvG.cred at k = 0 (Pm6DrvG.v:208) after the
   driver's 65536-byte buffer, with the ubsan layout's KPM = 8 and BOV = 3609042. *)
Lemma creditU_fits_driver : forall L n, hl_k_per_malloc L = 8 -> hl_b_overhead L = 3609042 -> 0 <= n < 2 ^ 26 ->
  10 * 8 + (8 + 4 * fst (pm_creditxU L n)) <= K0U - 8 /\
  (2 ^ 27 - 2 * 65536) + 10 * 3609042 + (n + 3609042 + 4 * snd (pm_creditxU L n)) <= B0U - (65536 + 3609042).
Proof.
  intros L n HK HB Hn. unfold pm_creditxU. cbn [fst snd].
  rewrite (kenc_g0 L), (benc_g0 L).
  rewrite HK, HB. unfold K0U, B0U, PMES.CLU. lia.
Qed.

(* Top: one library call consumes PHI (cf. PmLibIfaceAW.lib_call_okAW); credit and footprint are those of lib_pre /
   lib_post, so the layout's ll_credit carries pm_creditxU (lay_creditU). *)
Section Top.
Variable Lay : lib_layout.
Variable scfg : SpuriousCfg.
Variable HI : heap_iface.
Variable LSt : lib_statics.
Variable PHI : list byte -> Prop.

Definition lib_call_okU : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->
    PHI payload ->
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

Record lib_iface_okU : Prop := LIOKU {
  liou_call : lib_call_okU;
  liou_init : lib_statics_init Lay LSt;
  liou_frame : lib_statics_frame Lay LSt
}.
End Top.

Definition lay_creditU (L : heap_layout) (Lay : lib_layout) : Prop := forall n, ll_credit Lay n = pm_creditxU L n.

End LCU.
