(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoMainCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSOC.
Abbreviation IC := PMLA.C_casan.

Module PSOA_TOP.
Section T.
Context {SCFG_P : ScfgP}.

Theorem parse_some_ok (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL0 : icpt_layout) :
  PmHeapIfaceA.asan_iface_ok L ar C SCFG HI -> L5A.as0_layout L C -> rt_img_shadow L IL0 HI ->
  Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) ISLOTS) (icl_poison IL0) ->
  (forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a) ->
  hl_stack_malloc L 4 = SM4 ->
  (forall (fx fx' : FPState) R pc M R' pc' M',
      msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx') ->
  hl_tp L = TP ->
  (forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a) ->
  aset_shadow_spec L ar SCFG HI SETSH 245 256 ->
  PMSA.errh_specA L ar HI ERRH -> PMSA.set_ec_specA L ar HI IC SETEC -> PMSA.str_push_back_specA L ar HI PUSHB -> PMSA.vec_push_specA L ar HI VPUSH ->
  PMSA.pop_state_specA L ar HI POPST -> PMSA.parent_specA L ar HI PARENT -> PMSA.skip_space_specA L ar HI IC SKIPSP ->
  PMSA.begin_object_specA L ar HI IC BOBJ -> PMSA.begin_array_specA L ar HI IC BARR -> PMSA.end_object_specA L ar HI IC EOBJ -> PMSA.end_array_specA L ar HI IC EARR ->
  PMSA.begin_member_specA L ar HI IC BMEMBER -> PMSA.parse_true_specA L ar HI IC PTRUE -> PMSA.parse_false_specA L ar HI IC PFALSE -> PMSA.parse_null_specA L ar HI IC PNULL ->
  PMSA.parse_string_specA L ar HI IC PSTRING -> PMSA.parse_number_specA L ar HI IC PNUMBER ->
  PMSA.end_integer_value_specA L ar HI IC ENDINT -> PMSA.end_fraction_value_specA L ar HI IC ENDFRAC ->
  PMSA.visit_null_specA L ar HI IC VNULL -> PMSA.visit_bool_specA L ar HI IC VBOOL ->
  PMSA.parse_some_specA L ar HI IC PC.
Proof.
  intros HIok LAY ISH POI FOOTC SM4_OK FPM TPV ERRNO_OK SETSH_OK ERRH_OK SETEC_OK PUSHB_OK VPUSH_OK POPST_OK PARENT_OK SKIPSP_OK BOBJ_OK BARR_OK EOBJ_OK EARR_OK
    BMEMBER_OK PTRUE_OK PFALSE_OK PNULL_OK PSTRING_OK PNUMBER_OK ENDINT_OK ENDFRAC_OK VNULL_OK VBOOL_OK.
  unfold PMSA.parse_some_specA, PMSA.ptranseA, PMSA.ptrans_geA, PMSA.ptrans_gbeA, PMSA.cps_asan.
  intros LBo FF LK cr A sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  destruct PRE as (((Ha0 & Ha1 & Ha2) & HMORE) & H32 & Hstksh & HPA & HPSH & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3).
  specialize (H32 eq_refl).
  unfold PMSA.stksh, PMSA.parser_at, PMSA.parser_sh, PMSA.win_okA, PMSA.vis_at, PMSA.ec_at, PMSA.ls_ok, PMSA.fobj, PMSA.a0, PMSA.a1, PMSA.a2, PMSA.std_args in *.

  assert (EX : exists ch winb,
      match PML.ps_win ps with
      | Some (p, e) => In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384
      | None => ch = 0 end /\
      L5.bytes_at (hl_segs L) M (PSOI.wlo (PML.ps_win ps)) winb /\ Z.of_nat (length winb) = PSOI.whi (PML.ps_win ps) - PSOI.wlo (PML.ps_win ps)).
  { pose proof HWIN as HW. unfold PMLA.win_okA in HW.
    destruct (PML.ps_win ps) as [[p e]|] eqn:Hw.
    - destruct HW as (ch & INch & CH1 & CH2 & WDEF & CHSH).
      destruct (PTB.pa_win_some L IC M P ps HPA p e Hw) as (_ & _ & PE').
      destruct (PTA.defined_bytes (hl_segs L) M p (Z.to_nat (e - p)) ltac:(rewrite Z2Nat.id by (clear - PE'; lia); exact WDEF)) as (winb & WL & WB).
      exists ch, winb. cbn [PSOI.wlo PSOI.whi]. split; [exact (conj INch (conj CH1 (conj CH2 (conj WDEF CHSH))))|]. split; [exact WB|]. rewrite WL. apply Z2Nat.id. clear - PE'; lia.
    - exists 0, []. cbn [PSOI.wlo PSOI.whi]. split; [reflexivity|]. split; [intros i Hi; cbn [length] in Hi; lia | reflexivity]. }
  destruct EX as (ch & winb & HCH & Hwinb).
  exact (PSOM.main_open (PSOI.Inst _ L ar C HI IL0 HIok LAY ISH POI FOOTC SM4_OK FPM TPV ERRNO_OK SETSH_OK ERRH_OK SETEC_OK PUSHB_OK VPUSH_OK POPST_OK PARENT_OK SKIPSP_OK
                 BOBJ_OK BARR_OK EOBJ_OK EARR_OK BMEMBER_OK PTRUE_OK PFALSE_OK PNULL_OK PSTRING_OK PNUMBER_OK ENDINT_OK ENDFRAC_OK VNULL_OK VBOOL_OK
                 LBo FF LK cr A sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
                 Ha0 Ha1 Ha2 HMORE H32 Hstksh HPA HPSH HWF HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3 ch winb HCH Hwinb Hcont) (fun pc (H : In pc PSOM.OPEN_CALLS) => match H with end)).
Qed.
End T.
End PSOA_TOP.
