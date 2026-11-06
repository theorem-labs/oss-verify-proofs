(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA PsoInstXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXAW PsoMainXAW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSOC.
Abbreviation IC := PMLA.C_xasan.
Abbreviation mem := (word -> option byte).

Module PSOAW_TOP.
Section T.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma ex_un : forall segs (M : mem) a (n : nat), (n <= 8)%nat -> L5.defined M a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros segs M a n Hn HD H0 H1. destruct (PTA.defined_bytes segs M a n HD) as (bs & Hlen & HB).
  pose proof (L5C.bytes_at_rdn segs M bs a H0 ltac:(rewrite Hlen; exact H1) HB) as RD. rewrite Hlen in RD.
  exists (bytes_le_to_Z (map (fun z => Z_to_bv 8 z) bs)). pose proof (AX2S.bytes_le_to_Z_bound (map (fun z => Z_to_bv 8 z) bs)) as BND. rewrite length_map, Hlen in BND.
  split; [exact BND|]. rewrite RD. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [rewrite length_map; exact Hlen | exact Hn].
Qed.
Lemma ex_u8 : forall segs (M : mem) a, L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 8 /\ L5.u8_at segs M a v.
Proof.
  intros segs M a HD H0 H1. destruct (ex_un segs M a 1 ltac:(lia) HD H0 H1) as (v & Hv & RD). exists v. split; [exact Hv|].
  unfold L5.u8_at. rewrite RD. rewrite (CL5A.bytes1 v) by (clear - Hv; lia). reflexivity.
Qed.

Theorem parse_some_okw (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL0 : icpt_layout)
    (enc_invA : mem -> Z -> Z -> PMES.eghost -> Prop) (benc : PMES.eghost -> Z) (eroomA : PMES.eghost -> PMES.eev -> Prop) (CLA : Z) :      (* [comment removed for export] *)
  PmHeapIfaceA.asan_iface_ok L ar C SCFG HI -> L5A.as0_layout L C -> rt_img_shadow L IL0 HI ->
  Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) ISLOTS) (icl_poison IL0) ->
  (forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a) ->
  hl_stack_malloc L 4 = SM4 ->
  (forall (fx fx' : FPState) R pc M R' pc' M',
      msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx') ->
  hl_tp L = TP ->
  (forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static L a) ->
  aset_shadow_spec L ar SCFG HI SETSH 245 256 ->
  PMXA.enc_agreeP enc_invA -> PMXA.bencP benc -> PMXAW.roomwP eroomA CLA ->      (* [comment removed for export] *)
  PMXA.visit_null_specXA L ar HI IC enc_invA XKA.VIS XKA.VISD benc eroomA VNULL -> PMXA.visit_bool_specXA L ar HI IC enc_invA XKA.VIS XKA.VISD benc eroomA VBOOL ->
  PMSA.errh_specA L ar HI ERRH -> PMSA.set_ec_specA L ar HI IC SETEC -> PMSA.str_push_back_specA L ar HI PUSHB -> PMSA.vec_push_specA L ar HI VPUSH ->
  PMSA.pop_state_specA L ar HI POPST -> PMSA.parent_specA L ar HI PARENT -> PMXAW.skip_space_spec2AW L ar HI IC (PMRXA.the_rmA L) SKIPSP ->
  PMXAW.begin_object_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA BOBJ -> PMXAW.begin_array_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA BARR ->
  PMXAW.end_object_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA EOBJ -> PMXAW.end_array_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA EARR ->
  PMXAW.begin_member_specAW L ar HI IC (PMRXA.the_rmA L) BMEMBER ->
  PMXAW.parse_true_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PTRUE -> PMXAW.parse_false_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PFALSE ->
  PMXAW.parse_null_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PNULL ->
  PMXAW.parse_string_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PSTRING -> PMXAW.parse_number_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PNUMBER ->
  PMXAW.end_integer_value_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA ENDINT -> PMXAW.end_fraction_value_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA ENDFRAC ->
  PMXAW.parse_some_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PC.
Proof.
  intros HIok LAY ISH POI FOOTXC SM4_OK FPM TPV ERRNO_OK SETSH_OK ENC_AGREE BENC0 ROOMW VNULL_OK VBOOL_OK ERRH_OK SETEC_OK PUSHB_OK VPUSH_OK POPST_OK PARENT_OK SKIPSP_OK BOBJ_OK BARR_OK
    EOBJ_OK EARR_OK BMEMBER_OK PTRUE_OK PFALSE_OK PNULL_OK PSTRING_OK PNUMBER_OK ENDINT_OK ENDFRAC_OK.
  unfold PMXAW.parse_some_specXAW, PMXAW.ptransxeAW, PMXAW.ptrans_gxeAW, PMXAW.ptrans_gbxeAW, PMSA.cps_asan.
  intros LBo FF LK cr A sp r P V E S2 B kx bx g ps eg ww xw cw fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  destruct PRE as (((Ha0 & Ha1 & Ha2) & HMORE) & H32 & Hstksh & HPA & HPSH & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HINV & HLIT & HSYNC & Hkx & Hbx & HPC
                   & OP & OVX & OE & OS2 & AP1X & AP2 & AP3X & AP4 & AP5 & AP6 & HWB & HRM & HW4).      (* [comment removed for export] *)
  specialize (H32 eq_refl).
  unfold PMSA.stksh, PMSA.parser_at, PMSA.parser_sh, PMSA.win_okA, PMSA.vis_at, PMSA.ec_at, PMSA.ls_ok, PMSA.fobj, PMSA.a0, PMSA.a1, PMSA.a2, PMSA.std_args, PMES.ENC_SIZE in *.
  (* [comment removed for export] *)
  assert (OV : PMLA.fobj M FF V 8).
  { destruct OVX as (Vfr & V8 & Vsh). split; [exact (CL5A.ainfr_sub FF V 408 V 8 Vfr ltac:(clear; lia) ltac:(clear; lia)) | split; [exact V8 | intros j Hj; apply Vsh; clear - Hj; lia]]. }
  assert (AP1 : PMLA.apart P 272 V 8) by (unfold PMLA.apart in *; clear - AP1X; lia).
  assert (AP3 : PMLA.apart V 8 E 16) by (unfold PMLA.apart in *; clear - AP3X; lia).
  (* [comment removed for export] *)
  assert (EX : exists ch winb,
      match PML.ps_win ps with
      | Some (p, e) => In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384
      | None => ch = 0 end /\
      L5.bytes_at (hl_segs L) M (PSOIW.wlo (PML.ps_win ps)) winb /\ Z.of_nat (length winb) = PSOIW.whi (PML.ps_win ps) - PSOIW.wlo (PML.ps_win ps)).
  { pose proof HWIN as HW. unfold PMLA.win_okA in HW.
    destruct (PML.ps_win ps) as [[p e]|] eqn:Hw.
    - destruct HW as (ch & INch & CH1 & CH2 & WDEF & CHSH).
      destruct (PTB.pa_win_some L IC M P ps HPA p e Hw) as (_ & _ & PE').
      destruct (PTA.defined_bytes (hl_segs L) M p (Z.to_nat (e - p)) ltac:(rewrite Z2Nat.id by (clear - PE'; lia); exact WDEF)) as (winb & WL & WB).
      exists ch, winb. cbn [PSOIW.wlo PSOIW.whi]. split; [exact (conj INch (conj CH1 (conj CH2 (conj WDEF CHSH))))|]. split; [exact WB|]. rewrite WL. apply Z2Nat.id. clear - PE'; lia.
    - exists 0, []. cbn [PSOIW.wlo PSOIW.whi]. split; [reflexivity|]. split; [intros i Hi; cbn [length] in Hi; lia | reflexivity]. }
  destruct EX as (ch & winb0 & HCH & Hwinb0).
  (* [comment removed for export] *)
  assert (Hwinb : L5.bytes_at (hl_segs L) M (PSOIW.wlo (PML.ps_win ps)) ww /\ Z.of_nat (length ww) = PSOIW.whi (PML.ps_win ps) - PSOIW.wlo (PML.ps_win ps)).
  { pose proof HWB as X. unfold PMXAW.win_bytesA in X. destruct (PML.ps_win ps) as [[p e]|]; cbn [PSOIW.wlo PSOIW.whi].
    - destruct X as (X1 & X2 & _). exact (conj X1 X2).
    - rewrite X. split; [intros i Hi; cbn [length] in Hi; lia | reflexivity]. }
  assert (Hwrng : Forall (fun b => 0 <= b <= 255) ww).
  { pose proof HWB as X. unfold PMXAW.win_bytesA in X. destruct (PML.ps_win ps) as [[p e]|]; [exact (proj2 (proj2 X)) | rewrite X; constructor]. }
  set (winb := ww) in Hwinb.
  (* [comment removed for export] *)
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CL5A.infr_rng L ar _ FF P 272 RFx (proj1 OP) ltac:(clear; lia)) as (_ & _ & O3 & _ & _ & O6 & _).
  destruct (ex_u8 (hl_segs L) M (P + 220) ltac:(intros y Hy; replace (P + 220 + y) with (P + (220 + y)) by (clear; lia); apply (PTB.pa_def L IC M P ps HPA); clear - Hy; lia)
              ltac:(clear - O3; lia) ltac:(clear - O6; lia)) as (tag & Rtag & Htag).
  exact (PSOM.main_open (PSOIW.Inst _ L ar C HI IL0 HIok LAY ISH POI FOOTXC SM4_OK FPM TPV ERRNO_OK SETSH_OK enc_invA benc eroomA ENC_AGREE BENC0 CLA ROOMW VNULL_OK VBOOL_OK
                 ERRH_OK SETEC_OK PUSHB_OK VPUSH_OK POPST_OK PARENT_OK SKIPSP_OK BOBJ_OK BARR_OK EOBJ_OK EARR_OK BMEMBER_OK PTRUE_OK PFALSE_OK PNULL_OK PSTRING_OK PNUMBER_OK ENDINT_OK ENDFRAC_OK
                 LBo FF LK cr A sp r P V E S2 B kx bx g ps eg fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
                 Ha0 Ha1 Ha2 HMORE H32 Hstksh HPA HPSH HWF HWIN HBB HVIS HEC HLS HG HINV HLIT HSYNC Hkx Hbx HPC OP OV OVX OE OS2 AP1 AP1X AP2 AP3 AP3X AP4 AP5 AP6
                 ch winb tag HCH Hwinb (conj Htag Rtag) xw cw Hwrng HRM HW4 eg Hcont)
           (fun pc (H : In pc PSOM.OPEN_CALLS) => match H with end)).
Qed.
End T.
End PSOAW_TOP.
