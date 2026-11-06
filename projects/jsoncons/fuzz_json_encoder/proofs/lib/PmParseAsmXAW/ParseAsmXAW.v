(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  HeapIface HeapIfaceA L5Defs L5Core Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA PsoInstXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXAW ParseSomeXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SkipSpace2XAW BeginMemberXAW AfterValueXAW EndObjectXAW EndArrayXAW ParseTrueXAW ParseFalseXAW ParseNullXAW EndStringValueXAW
  EndPositiveValueXAW EndNegativeValueXAW EndIntegerValueXAW EndFractionValueXAW ParseNumberXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import BeginObjectXAW BeginArrayXAW PswSpecsXA AtcXAW ConvertXAW ParseStringXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require Import ValidateXAW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import PSOC.
Abbreviation IC := PMLA.C_xasan.
Abbreviation VIS := XKA.VIS.
Abbreviation VISD := XKA.VISD.

Section Asm.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL : icpt_layout).
Variable CLW : Z.
Variables (enc_invA : (word -> option byte) -> Z -> Z -> PMES.eghost -> Prop) (benc : PMES.eghost -> Z) (eroomA : PMES.eghost -> PMES.eev -> Prop).
(* [comment removed for export] *)
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Hypothesis FOOTXC : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a.
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis TPV : hl_tp L = 6938576.
(* [comment removed for export] *)
Definition VTSLOTS : list Z := [1420344; 1420352; 1420360; 1420368; 1420376; 1420384; 1420400; 1420408; 1420416; 1420424; 1420432; 1420440;
                               1421176; 1421336; 1421344; 1421360; 1421632; 1421640; 1421648; 1421656; 1421672; 1421688; 1421696; 1421704; 1421712; 1421720; 1421728;
                               1435608; 1435760; 1435840; 1435864].
Hypothesis POI_VT : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) VTSLOTS) (icl_poison IL).
Hypothesis POI_DTAB : Forall (fun r : Z * Z => 165728 + 256 <= fst r \/ snd r <= 165728) (icl_poison IL).
Hypothesis POI_TC : Forall (fun r : Z * Z => 151376 + 288 <= fst r \/ snd r <= 151376) (icl_poison IL).     (* [comment removed for export] *)
Hypothesis SM0 : hl_stack_malloc L 0 = 0x65e70.
Hypothesis SM1 : hl_stack_malloc L 1 = 0x65fe4.
Hypothesis SM4 : hl_stack_malloc L 4 = 0x664bc.
Hypothesis SETSHF5 : aset_shadow_spec L ar SCFG HI 540344 245 256.
Hypothesis ERRNO_OK : forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a.      (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ERRH : PMSA.errh_specA L ar HI 836392.
Hypothesis SETEC : PMSA.set_ec_specA L ar HI IC 827600.
Hypothesis STRPUSHBACK : PMSA.str_push_back_specA L ar HI 1041292.
Hypothesis STRAPPEND : PMSA.str_append_specA L ar HI 1040708.
Hypothesis STRAPPENDRANGE : PMSA.str_append_range_specA L ar HI 911564.
Hypothesis VPUSH : PMSA.vec_push_specA L ar HI 841320.
Hypothesis POPSTATE : PMSA.pop_state_specA L ar HI 878496.
Hypothesis PARENT : PMSA.parent_specA L ar HI 899700.
Hypothesis DECSTR : PMSA.decstr_to_double_specA L ar HI IC 824664.
Hypothesis DECU64 : PMSA.dec_u64_specA L ar HI IC 904392.
Hypothesis TCE : PMSA.translate_conv_errc_specA L ar HI IC 910144.
(* [comment removed for export] *)
Hypothesis ENC_AGREE : PMXA.enc_agreeP enc_invA.
Hypothesis BENC0 : PMXA.bencP benc.
Hypothesis ROOMW : PMXAW.roomwP eroomA CLW.      (* [comment removed for export] *)
Hypothesis VNULL : PMXA.visit_null_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751316.
Hypothesis VBOOL : PMXA.visit_bool_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751920.
Hypothesis VU64 : PMXA.visit_uint64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 738876.
Hypothesis VI64 : PMXA.visit_int64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 739428.
Hypothesis VSTR : PMXA.visit_string_specXA L ar HI IC enc_invA VIS VISD benc eroomA 752584.
Hypothesis VKEY : PMXA.visit_key_specXA L ar HI IC enc_invA VIS VISD benc eroomA 749552.
Hypothesis VDBL : PMXA.visit_double_specXA L ar HI IC enc_invA VIS VISD benc eroomA 739980.
Hypothesis VBOBJ : PMXA.visit_begin_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 744592.
Hypothesis VBARR : PMXA.visit_begin_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 747704.
Hypothesis VEOBJ : PMXA.visit_end_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 746348.
Hypothesis VEARR : PMXA.visit_end_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 737520.

Lemma FPMH : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Proof. rewrite (L5A.aly_segs L C LAY). exact FPM. Qed.
(* [comment removed for export] *)
Lemma POIV : forall a, existsb (Z.eqb a) VTSLOTS = true -> Forall (fun r : Z * Z => a + 8 <= fst r \/ snd r <= a) (icl_poison IL).
Proof.
  intros a Ha. apply existsb_exists in Ha as (b & Hb1 & Hb2). apply Z.eqb_eq in Hb2. subst b.
  eapply Forall_impl; [|exact POI_VT]. cbv beta. intros r Hr. exact (proj1 (Forall_forall _ _) Hr a Hb1).
Qed.
Lemma POIL : forall l, forallb (fun a => existsb (Z.eqb a) VTSLOTS) l = true -> Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) l) (icl_poison IL).
Proof.
  intros l Hl. rewrite forallb_forall in Hl. eapply Forall_impl; [|exact POI_VT]. cbv beta. intros r Hr. apply Forall_forall. intros a Ha.
  pose proof (Hl a Ha) as Hb. apply existsb_exists in Hb as (b & Hb1 & Hb2). apply Z.eqb_eq in Hb2. subst b. exact (proj1 (Forall_forall _ _) Hr a Hb1).
Qed.
Lemma POI_TC264 : Forall (fun r : Z * Z => 151376 + 264 <= fst r \/ snd r <= 151376) (icl_poison IL).
Proof. eapply Forall_impl; [|exact POI_TC]. cbv beta. intros r Hr. lia. Qed.
(* [comment removed for export] *)
Ltac hyp := first
  [ exact HIok | exact LAY | exact FPM | exact FPMH | exact FOOTC | exact FOOTXC | exact ISH | exact TPV | exact POI_DTAB | exact SM0 | exact SM1 | exact SM4 | exact SETSHF5 | exact ERRNO_OK
  | exact ERRH | exact SETEC | exact STRPUSHBACK | exact STRAPPEND | exact STRAPPENDRANGE | exact VPUSH | exact POPSTATE | exact PARENT | exact DECSTR | exact DECU64 | exact TCE
  | exact ENC_AGREE | exact BENC0 | exact ROOMW | exact eroomA
  | exact VNULL | exact VBOOL | exact VU64 | exact VI64 | exact VSTR | exact VKEY | exact VDBL | exact VBOBJ | exact VBARR | exact VEOBJ | exact VEARR
  | exact POI_TC264 | apply POIV; vm_compute; reflexivity | apply POIL; vm_compute; reflexivity | (pose proof (L5A.aly_cost L C LAY); lia)
  | match goal with |- ?g => idtac "OPEN" g; fail end ].


Theorem parse_some_okw_lib : PMXAW.parse_some_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW PC.
Proof.
  (* [comment removed for export] *)
  eassert (AVW : PMXAW.after_value_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (AfterValueXAW.after_value_okw L ar C HI); hyp).
  eassert (VALW : PMXAW.validate_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (ValidateXAW.validate_okw L ar C HI); hyp).
  eassert (ESVW : PMXAW.end_string_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndStringValueXAW.end_string_value_okw L ar C HI); first [exact VALW | hyp]).
  eassert (EPOSW : PMXAW.end_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _ _) by (eapply (EndPositiveValueXAW.end_positive_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (ENEGW : PMXAW.end_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _ _) by (eapply (EndNegativeValueXAW.end_negative_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (EINTW : PMXAW.end_integer_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndIntegerValueXAW.end_integer_value_okw L ar C HI); first [exact EPOSW | exact ENEGW | hyp]).
  eassert (EFRACW : PMXAW.end_fraction_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndFractionValueXAW.end_fraction_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (ATCW : PSWS.atc_specXAW L ar HI IC _) by (eapply (AtcXAW.atc_okw L ar C HI); hyp).
  eassert (CONVW : PSWS.convert_specXAW L ar HI _) by (eapply (ConvertXAW.convert_okw L ar C HI); hyp).
  eassert (PSTRW : PMXAW.parse_string_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseStringXAW.parse_string_okw L ar C HI); first [exact ATCW | exact CONVW | exact ESVW | hyp]).
  eassert (PNUMW : PMXAW.parse_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseNumberXAW.parse_number_okw L ar C HI); first [exact EINTW | exact EFRACW | hyp]).
  eassert (SKIPW : PMXAW.skip_space_spec2AW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (SkipSpace2XAW.skip_space_okw L ar C HI); hyp).
  eassert (BOBJW : PMXAW.begin_object_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (BeginObjectXAW.begin_object_okw L ar C HI); hyp).
  eassert (BARRW : PMXAW.begin_array_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (BeginArrayXAW.begin_array_okw L ar C HI); hyp).
  eassert (EOBJW : PMXAW.end_object_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndObjectXAW.end_object_okw L ar C HI); hyp).
  eassert (EARRW : PMXAW.end_array_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndArrayXAW.end_array_okw L ar C HI); hyp).
  eassert (BMEMW : PMXAW.begin_member_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (BeginMemberXAW.begin_member_okw L ar C HI); hyp).
  eassert (PTRUEW : PMXAW.parse_true_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseTrueXAW.parse_true_okw L ar C HI); hyp).
  eassert (PFALSEW : PMXAW.parse_false_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseFalseXAW.parse_false_okw L ar C HI); hyp).
  eassert (PNULLW : PMXAW.parse_null_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseNullXAW.parse_null_okw L ar C HI); hyp).
  eapply (PSOAW_TOP.parse_some_okw L ar C HI IL enc_invA benc eroomA CLW);
    first [ exact SKIPW | exact BOBJW | exact BARRW | exact EOBJW | exact EARRW | exact BMEMW | exact PTRUEW | exact PFALSEW | exact PNULLW
          | exact PSTRW | exact PNUMW | exact EINTW | exact EFRACW | hyp ].
Qed.
End Asm.
Print Assumptions parse_some_okw_lib.
