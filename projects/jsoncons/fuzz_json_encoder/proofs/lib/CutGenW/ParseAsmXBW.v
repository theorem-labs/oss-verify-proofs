(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  HeapIface HeapIfaceA L5Defs L5Core Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA PsoInstXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PmLibSpecsBLocal.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXBW ParseSomeXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SkipSpace2XBW BeginMemberXBW AfterValueXBW EndObjectXBW EndArrayXBW ParseTrueXBW ParseFalseXBW ParseNullXBW EndStringValueXBW
  EndPositiveValueXBW EndNegativeValueXBW EndIntegerValueXBW EndFractionValueXBW ParseNumberXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import BeginObjectXBW BeginArrayXBW PswSpecsXB AtcXBW ConvertXBW ParseStringXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require Import ValidateXBW.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import PSOC.
Abbreviation IC := PMLA.C_xboth.
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
Hypothesis TPV : hl_tp L = 6953104.
(* [comment removed for export] *)
Definition VTSLOTS : list Z := [1435224; 1435232; 1435240; 1435248; 1435256; 1435264; 1435280; 1435288; 1435296; 1435304; 1435312; 1435320;
                               1436056; 1436216; 1436224; 1436240; 1436512; 1436520; 1436528; 1436536; 1436552; 1436568; 1436576; 1436584; 1436592; 1436600; 1436608;
                               1450200; 1450352; 1450432; 1450456].
Hypothesis POI_VT : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) VTSLOTS) (icl_poison IL).
Hypothesis POI_DTAB : Forall (fun r : Z * Z => 166144 + 256 <= fst r \/ snd r <= 166144) (icl_poison IL).
Hypothesis POI_TC : Forall (fun r : Z * Z => 151792 + 288 <= fst r \/ snd r <= 151792) (icl_poison IL).     (* [comment removed for export] *)
Hypothesis POI_CVT : Forall (fun r : Z * Z => 166496 + 8 <= fst r \/ snd r <= 166496) (icl_poison IL).     (* [comment removed for export] *)
Hypothesis SM0 : hl_stack_malloc L 0 = 0x66740.
Hypothesis SM1 : hl_stack_malloc L 1 = 0x668b4.
Hypothesis SM4 : hl_stack_malloc L 4 = 0x66d8c.
Hypothesis SETSHF5 : aset_shadow_spec L ar SCFG HI 542600 245 256.
Hypothesis ERRNO_OK : forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a.      (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ERRH : PMSA.errh_specA L ar HI 852452.
Hypothesis SETEC : PMSA.set_ec_specA L ar HI IC 842884.
Hypothesis STRPUSHBACK : PMSA.str_push_back_specA L ar HI 1056004.
Hypothesis STRAPPEND : PMSA.str_append_specA L ar HI 1055420.
Hypothesis STRAPPENDRANGE : PMSA.str_append_range_specA L ar HI 926224.
Hypothesis VPUSH : PMSA.vec_push_specA L ar HI 858048.
Hypothesis POPSTATE : PMSB.pop_state_specA L ar HI 893820.
Hypothesis PARENT : PMSA.parent_specA L ar HI 914208.
Hypothesis DECSTR : PMSA.decstr_to_double_specA L ar HI IC 839740.
Hypothesis DECU64 : PMSA.dec_u64_specA L ar HI IC 918912.
Hypothesis TCE : PMSA.translate_conv_errc_specA L ar HI IC 925292.
(* [comment removed for export] *)
Hypothesis ENC_AGREE : PMXA.enc_agreeP enc_invA.
Hypothesis BENC0 : PMXA.bencP benc.
Hypothesis ROOMW : PMXAW.roomwP eroomA CLW.      (* [comment removed for export] *)
Hypothesis VNULL : PMXA.visit_null_specXA L ar HI IC enc_invA VIS VISD benc eroomA 756100.
Hypothesis VBOOL : PMXA.visit_bool_specXA L ar HI IC enc_invA VIS VISD benc eroomA 756716.
Hypothesis VU64 : PMXA.visit_uint64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 741900.
Hypothesis VI64 : PMXA.visit_int64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 742460.
Hypothesis VSTR : PMXA.visit_string_specXA L ar HI IC enc_invA VIS VISD benc eroomA 757412.
Hypothesis VKEY : PMXA.visit_key_specXA L ar HI IC enc_invA VIS VISD benc eroomA 754188.
Hypothesis VDBL : PMXA.visit_double_specXA L ar HI IC enc_invA VIS VISD benc eroomA 743020.
Hypothesis VBOBJ : PMXA.visit_begin_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 747548.
Hypothesis VBARR : PMXA.visit_begin_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751264.
Hypothesis VEOBJ : PMXA.visit_end_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 749780.
Hypothesis VEARR : PMXA.visit_end_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 740416.

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
Lemma POI_TC264 : Forall (fun r : Z * Z => 151792 + 264 <= fst r \/ snd r <= 151792) (icl_poison IL).
Proof. eapply Forall_impl; [|exact POI_TC]. cbv beta. intros r Hr. lia. Qed.
(* [comment removed for export] *)
Ltac hyp := first
  [ exact HIok | exact LAY | exact FPM | exact FPMH | exact FOOTC | exact FOOTXC | exact ISH | exact TPV | exact POI_DTAB | exact SM0 | exact SM1 | exact SM4 | exact SETSHF5 | exact ERRNO_OK
  | exact ERRH | exact SETEC | exact STRPUSHBACK | exact STRAPPEND | exact STRAPPENDRANGE | exact VPUSH | exact POPSTATE | exact PARENT | exact DECSTR | exact DECU64 | exact TCE
  | exact ENC_AGREE | exact BENC0 | exact ROOMW | exact eroomA
  | exact VNULL | exact VBOOL | exact VU64 | exact VI64 | exact VSTR | exact VKEY | exact VDBL | exact VBOBJ | exact VBARR | exact VEOBJ | exact VEARR
  | exact POI_TC264 | exact POI_CVT | apply POIV; vm_compute; reflexivity | apply POIL; vm_compute; reflexivity | (pose proof (L5A.aly_cost L C LAY); lia)
  | match goal with |- ?g => idtac "OPEN" g; fail end ].


Theorem parse_some_okw_lib : PMXAW.parse_some_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW PC.
Proof.
  (* [comment removed for export] *)
  eassert (AVW : PMXAW.after_value_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (AfterValueXBW.after_value_okw L ar C HI); hyp).
  eassert (VALW : PMXAW.validate_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (ValidateXBW.validate_okw L ar C HI); hyp).
  eassert (ESVW : PMXAW.end_string_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndStringValueXBW.end_string_value_okw L ar C HI); first [exact VALW | hyp]).
  eassert (EPOSW : PMXAW.end_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _ _) by (eapply (EndPositiveValueXBW.end_positive_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (ENEGW : PMXAW.end_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _ _) by (eapply (EndNegativeValueXBW.end_negative_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (EINTW : PMXAW.end_integer_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndIntegerValueXBW.end_integer_value_okw L ar C HI); first [exact EPOSW | exact ENEGW | hyp]).
  eassert (EFRACW : PMXAW.end_fraction_value_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndFractionValueXBW.end_fraction_value_okw L ar C HI); first [exact AVW | hyp]).
  eassert (ATCW : PSWS.atc_specXAW L ar HI IC _) by (eapply (AtcXBW.atc_okw L ar C HI); hyp).
  eassert (CONVW : PSWS.convert_specXAW L ar HI IC _) by (eapply (ConvertXBW.convert_okw L ar C HI); hyp).
  eassert (PSTRW : PMXAW.parse_string_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseStringXBW.parse_string_okw L ar C HI); first [exact ATCW | exact CONVW | exact ESVW | hyp]).
  eassert (PNUMW : PMXAW.parse_number_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseNumberXBW.parse_number_okw L ar C HI); first [exact EINTW | exact EFRACW | hyp]).
  eassert (SKIPW : PMXAW.skip_space_spec2AW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (SkipSpace2XBW.skip_space_okw L ar C HI); hyp).
  eassert (BOBJW : PMXAW.begin_object_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (BeginObjectXBW.begin_object_okw L ar C HI); hyp).
  eassert (BARRW : PMXAW.begin_array_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (BeginArrayXBW.begin_array_okw L ar C HI); hyp).
  eassert (EOBJW : PMXAW.end_object_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndObjectXBW.end_object_okw L ar C HI); hyp).
  eassert (EARRW : PMXAW.end_array_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (EndArrayXBW.end_array_okw L ar C HI); hyp).
  eassert (BMEMW : PMXAW.begin_member_specAW L ar HI IC (PMRXA.the_rmA L) _) by (eapply (BeginMemberXBW.begin_member_okw L ar C HI); hyp).
  eassert (PTRUEW : PMXAW.parse_true_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseTrueXBW.parse_true_okw L ar C HI); hyp).
  eassert (PFALSEW : PMXAW.parse_false_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseFalseXBW.parse_false_okw L ar C HI); hyp).
  eassert (PNULLW : PMXAW.parse_null_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW _) by (eapply (ParseNullXBW.parse_null_okw L ar C HI); hyp).
  eapply (PSOAW_TOP.parse_some_okw L ar C HI IL enc_invA benc eroomA CLW);
    first [ exact SKIPW | exact BOBJW | exact BARRW | exact EOBJW | exact EARRW | exact BMEMW | exact PTRUEW | exact PFALSEW | exact PNULLW
          | exact PSTRW | exact PNUMW | exact EINTW | exact EFRACW | hyp ].
Qed.
End Asm.
Print Assumptions parse_some_okw_lib.
