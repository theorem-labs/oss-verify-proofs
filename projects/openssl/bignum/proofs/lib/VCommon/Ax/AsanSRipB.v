(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec StepTac SeqExec CatExec StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSLibc AsanSMat AsanSMiz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanSRipA AsanSRipA1 AsanSRipA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Section Rip.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Local Notation h := (b - 0x48c)%Z.
Variable z : Z.
Variables gK gMB gME gHE aK aMB aME aHE : Z.
Hypothesis HW : words_ok segs b RIP_WORDS = true.
Hypothesis HWh : words_ok segs h HLP_WORDS = true.
Hypothesis HWz : words_ok segs z MIZ_WORDS = true.
Hypothesis HJz : jal_ok segs b 0x170 1 z = true.
Hypothesis HPh0 : pair_ok segs h 0x0 11 11 gK = true.
Hypothesis HPh20 : pair_ok segs h 0x20 13 13 gMB = true.
Hypothesis HPh28 : pair_ok segs h 0x28 14 14 gME = true.
Hypothesis HPh44 : pair_ok segs h 0x44 14 14 gHE = true.
Hypothesis HP2c : pair_ok segs b 0x2c 10 21 gK = true.
Hypothesis HP4c : pair_ok segs b 0x4c 13 13 gMB = true.
Hypothesis HP54 : pair_ok segs b 0x54 14 14 gME = true.
Hypothesis HP70 : pair_ok segs b 0x70 14 14 gHE = true.
Hypothesis HP94 : pair_ok segs b 0x94 12 12 gMB = true.
Hypothesis HP9c : pair_ok segs b 0x9c 13 13 gME = true.
Hypothesis HPb8 : pair_ok segs b 0xb8 13 13 gHE = true.
Hypothesis Hgb : (0 <= gK < 2 ^ 60 /\ 0 <= gMB < 2 ^ 60 /\ 0 <= gME < 2 ^ 60 /\ 0 <= gHE < 2 ^ 60 /\
                  0 <= aK < 2 ^ 60 /\ 0 <= aMB < 2 ^ 60 /\ 0 <= aME < 2 ^ 60 /\ 0 <= aHE < 2 ^ 60)%Z.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get_l segs b RIP_WORDS); [exact HW | reflexivity | reflexivity].
Local Ltac fwh := apply (words_get_l segs h HLP_WORDS); [exact HWh | reflexivity | reflexivity].

Lemma F_e8 : fetch_word segs (pcw b 0xe8) = Some (Z_to_bv 32 0x00050993). Proof. fw. Qed.
Lemma F_ec : fetch_word segs (pcw b 0xec) = Some (Z_to_bv 32 0x000a0513). Proof. fw. Qed.
Lemma F_f0 : fetch_word segs (pcw b 0xf0) = Some (Z_to_bv 32 0xa85ff0ef). Proof. fw. Qed.
Lemma F_f4 : fetch_word segs (pcw b 0xf4) = Some (Z_to_bv 32 0x000ab583). Proof. fw. Qed.
Lemma F_f8 : fetch_word segs (pcw b 0xf8) = Some (Z_to_bv 32 0x00345613). Proof. fw. Qed.
Lemma F_fc : fetch_word segs (pcw b 0xfc) = Some (Z_to_bv 32 0x00c58633). Proof. fw. Qed.
Lemma F_100 : fetch_word segs (pcw b 0x100) = Some (Z_to_bv 32 0x00060603). Proof. fw. Qed.
Lemma F_104 : fetch_word segs (pcw b 0x104) = Some (Z_to_bv 32 0x00060663). Proof. fw. Qed.
Lemma F_110 : fetch_word segs (pcw b 0x110) = Some (Z_to_bv 32 0xfff90913). Proof. fw. Qed.
Lemma F_114 : fetch_word segs (pcw b 0x114) = Some (Z_to_bv 32 0x00395613). Proof. fw. Qed.
Lemma F_118 : fetch_word segs (pcw b 0x118) = Some (Z_to_bv 32 0x00c585b3). Proof. fw. Qed.
Lemma F_11c : fetch_word segs (pcw b 0x11c) = Some (Z_to_bv 32 0x00058583). Proof. fw. Qed.
Lemma F_120 : fetch_word segs (pcw b 0x120) = Some (Z_to_bv 32 0x04058263). Proof. fw. Qed.

Local Notation globals := (@AsanSRipA.globals segs gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation globals_nl := (@AsanSRipA.globals_nl gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation h_sum := (@AsanSRipA.h_sum segs cfg b gK gMB gME gHE aK aMB aME aHE HWh HPh0 HPh20 HPh28 HPh44 Hgb) (only parsing).

Ltac wpair P Hl Hv Hnl :=
  let wa := fresh "wa" in let wl := fresh "wl" in let ia := fresh "ia" in let il := fresh "il" in
  let HFa := fresh "HFa" in let HEa := fresh "HEa" in let HDa := fresh "HDa" in
  let HFl := fresh "HFl" in let HEl := fresh "HEl" in let HDl := fresh "HDl" in let HA := fresh "HA" in
  destruct (pair_ok_sound _ _ _ _ _ _ P ltac:(lia)) as (wa & wl & ia & il & HFa & HEa & HDa & HFl & HEl & HDl & HA);
  eapply rzc_acc; [ assumption | first [ reflexivity | assumption ]
                  | eapply wacc_Auipc; [ fetch_tac HFa | exact HEa | exact HDa ] | apply acc_ok_nil | ];
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn;
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac HFl | exact HEl | exact HDl | rgn; rewrite HA, ?mem_setx; exact Hl ]
                  | rgn; rewrite HA; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

Ltac wvar F D Hl Hv Hnl :=
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | rgn; rewrite add_sext0, ?mem_setx; exact Hl ]
                  | rgn; rewrite add_sext0; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

Section Main.
Variable model0 : Model.
Hypothesis Hh0 : m_halted model0 = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variables (beg : word) (size : Z) (sp0 : word).
Local Notation B := (bv_unsigned beg).
Local Notation SP := (bv_unsigned sp0).
Hypothesis Hsz : (1 <= size)%Z.
Hypothesis Hhi : (B + size + 8 <= 0x800000000000 /\ size <= 2 ^ 40)%Z.
Hypothesis Hreg : (0x10007fff8000 <= B \/ B + size + 8 <= 0x7fff8000)%Z.
Hypothesis H2 : rg ms0 2 = sp0.
Hypothesis Hg0 : globals (ms_mem ms0).
Hypothesis HgN : globals_nl model0.
Hypothesis Hsh : forall q, (0x7fff8000 + B / 8 <= q <= 0x7fff8000 + (B + size - 1) / 8)%Z ->
  bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hbud : (vm_backing_used model0 + 4096 * rpg size <= vm_limit (m_vmmaps model0))%Z.
Let Hrpg : (2 <= rpg size /\ 8 * (rpg size - 2) <= size)%Z.
Proof. pose proof (rpg_f size). lia. Qed.
Hypothesis Hsp : (0x10007fff8000 <= SP <= 0x800000000000)%Z.
Hypothesis Hok : store_ok segs (ms_mem ms0) (Z_to_bv 64 (SP - 72)) 72 = true.
Hypothesis HnlS : no_lazy model0 (SP - 72) SP.
Hypothesis Hdsh : (SP <= 0x7fff8000 + B / 8 \/ 0x7fff8000 + (B + size - 1) / 8 < SP - 72)%Z.
Hypothesis Hdg : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> (a + 8 <= SP - 72 \/ SP <= a)%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms' model', RPOST ms0 ms' (SP - 72) SP -> ms_pc_val ms' = rg ms0 1 -> rg ms' 10 = w0 ->
  mat_of model0 model' (rpg size) -> realizes_cfg segs cfg (mkCfg ms' model') T.

Hypothesis Hb : (0x10000 <= b /\ b + 0x20000 < 2 ^ 47 /\ b mod 4 = 0)%Z.
Local Notation K := 0x7fff8000%Z.
Local Notation E := (bv_unsigned beg + size)%Z.
Local Notation SB := (@AsanSRipA1.SB sp0) (only parsing).
Local Notation Mf := (@AsanSRipA1.Mf ms0 sp0) (only parsing).
Local Notation u_sp0 := (@AsanSRipA1.u_sp0 sp0) (only parsing).
Local Notation st_slot := (@AsanSRipA1.st_slot segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hok Hb) (only parsing).
Local Notation acc_slot := (@AsanSRipA1.acc_slot b model0 ms0 beg size sp0 Hsz Hhi Hreg Hsp HnlS Hb) (only parsing).
Local Notation Mf_out := (@AsanSRipA1.Mf_out b ms0 beg size sp0 Hsp) (only parsing).
Local Notation Mf_grows := (@AsanSRipA1.Mf_grows ms0 sp0) (only parsing).
Local Notation rdn_Mf_out := (@AsanSRipA1.rdn_Mf_out segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation cell8_Mf := (@AsanSRipA1.cell8_Mf segs b gK gMB gME gHE aK aMB aME aHE Hgb ms0 beg size sp0 Hsz Hhi Hreg Hsp Hdg Hb) (only parsing).
Local Notation globals_Mf := (@AsanSRipA1.globals_Mf segs b gK gMB gME gHE aK aMB aME aHE Hgb ms0 beg size sp0 Hsz Hhi Hreg Hg0 Hsp Hdsh Hdg Hb) (only parsing).
Local Notation shadow_Mf := (@AsanSRipA1.shadow_Mf segs b ms0 beg size sp0 Hsz Hhi Hreg Hsh Hsp Hdsh Hb) (only parsing).
Local Notation rdn_SB_same := (@AsanSRipA1.rdn_SB_same segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation rdn_SB_other := (@AsanSRipA1.rdn_SB_other segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read56 := (@AsanSRipA1.Mf_read56 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read48 := (@AsanSRipA1.Mf_read48 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read40 := (@AsanSRipA1.Mf_read40 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read32 := (@AsanSRipA1.Mf_read32 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read24 := (@AsanSRipA1.Mf_read24 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read16 := (@AsanSRipA1.Mf_read16 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read8 := (@AsanSRipA1.Mf_read8 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation BI := (@AsanSRipA2.BI model0 ms0) (only parsing).
Local Notation hclob_cases := (@AsanSRipA2.hclob_cases ) (only parsing).
Local Notation B6 := (@AsanSRipA2.B6 segs cfg b HW model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hsp HnlS Hra HK Hb) (only parsing).
Local Notation mat_of_trans := (@AsanSRipA2.mat_of_trans b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ra_even := (@AsanSRipA2.ra_even b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ab8 := (@AsanSRipA2.ab8 beg) (only parsing).
Local Notation ae8 := (@AsanSRipA2.ae8 beg size) (only parsing).
Local Notation bq := (@AsanSRipA2.bq beg) (only parsing).
Local Notation eq8 := (@AsanSRipA2.eq8 beg size) (only parsing).
Local Notation ab8_f := (@AsanSRipA2.ab8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ae8_f := (@AsanSRipA2.ae8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation bq_f := (@AsanSRipA2.bq_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation eq8_f := (@AsanSRipA2.eq8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation shadow_Mf' := (@AsanSRipA2.shadow_Mf' segs b ms0 beg size sp0 Hsz Hhi Hreg Hsh Hsp Hdsh Hb) (only parsing).
Local Notation B5 := (@AsanSRipA2.B5 segs cfg b z gK gMB gME gHE aK aMB aME aHE HW HWz HJz Hgb model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hsh Hbud Hsp Hok HnlS Hdsh Hra HK Hb) (only parsing).

Lemma srl3w : forall a : word, alu64 ALU_SRL a (zext 64 (@BV 6 3 I)) = Z_to_bv 64 (bv_unsigned a / 8).
Proof. intros a. rewrite <- (Z_to_bv_u a) at 1. apply srl3. apply (u64_range a). Qed.

Lemma wacc_Load_q : forall ms w isz sz sg rd rs1 (imm : bv 12) bs (a : word),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, isz) ->
  rg ms rs1 + sext 64 imm = a ->
  rdn segs (ms_mem ms) a (msz_n sz) = Some bs ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (load_word sz sg bs)
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) [(a, msz_n sz)]).
Proof. intros ms w isz sz sg rd rs1 imm bs a Hf He Hd Ha Hr. subst a. exact (wacc_Load segs ms w isz sz sg rd rs1 imm bs Hf He Hd Hr). Qed.

Lemma br_w0w0 : branch_taken BC_EQ w0 w0 = true.
Proof. reflexivity. Qed.

Lemma pgone : forall (a : word), (bv_unsigned a mod 4096 + Z.of_nat 1 <= 4096)%Z.
Proof. intros a. pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia. Qed.

Lemma lb_zero : load_word SZ1 true [Z_to_bv 8 0] = w0.
Proof. reflexivity. Qed.

Lemma globals_nl_mat : forall model k, mat_of model0 model k -> globals_nl model.
Proof.
  intros model k H. destruct HgN as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  repeat split; apply (no_lazy_mat model0 model k); assumption.
Qed.

Ltac wlsh F D q Hmat Hmem :=
  let model' := fresh "model'" in let Hm' := fresh "Hm'" in let Hmat' := fresh "Hmat'" in
  destruct (mat_step _ _ _ (Z_to_bv 64 q) 1 Hmat ltac:(lia) (pgone _) ltac:(pose proof (proj2 Hmat); lia))
    as (model' & Hm' & Hmat');
  let Hh' := fresh "Hh'" in
  pose proof (mat_of_halted _ _ _ Hmat') as Hh'; rewrite Hh0 in Hh';
  eapply rzc_mat;
  [ assumption | first [ reflexivity | assumption ]
  | eapply (wacc_Load_q _ _ _ _ _ _ _ _ _ (Z_to_bv 64 q));
    [ fetch_tac F | reflexivity | exact D | rgn; rewrite ?add_sext0; reflexivity
    | cbn [msz_n]; rewrite ?mem_setx, ?Hmem; apply rdn_1; apply shadow_Mf'; lia ]
  | exact Hm'
  | ];
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn; rewrite lb_zero.

Lemma B4 : forall ms model k, BI ms model k Mf -> (k = 0)%Z ->
  ms_pc_val ms = pcw b 0xf4 -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rg ms 8 = beg -> rg ms 18 = Z_to_bv 64 E -> rg ms 21 = Z_to_bv 64 aK ->
  rg ms 19 = Z_to_bv 64 (K + ab8) -> rg ms 10 = Z_to_bv 64 (K + ae8) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model k (HF & Hmat & Hk0) Hk Hpc Hsp2 H8 H18 H21 H19 H10. subst k.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg).
  pose proof ab8_f. pose proof ae8_f. pose proof bq_f. pose proof eq8_f.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model 0 Hmat); exact Hh0).
  pose proof (globals_nl_mat model 0 Hmat) as (N1 & NaK & _).
  pose proof globals_Mf as (_ & (laK & HlaK & HvaK) & _). rewrite <- Hmem in HlaK.
  eapply rzc_acc; [ assumption | assumption
    | eapply wacc_Load; [ fetch_tac F_f4 | reflexivity | exact D_000ab583 | rewrite H21, add_sext0; exact HlaK ]
    | rewrite H21, add_sext0; apply cell_nl; [lia | exact NaK] | ].
  rewrite Hpc; pcn; rewrite HvaK.
  wsx wacc_ShiftImm F_f8 D_00345613. rgn. rewrite H8, srl3w.
  wsx wacc_Op F_fc D_00c58633. rgn. rewrite alu_add, zw_add. change (bv_unsigned beg / 8)%Z with bq.
  wlsh F_100 D_00060603 (K + bq)%Z Hmat Hmem.
  wsx wacc_Branch F_104 D_00060663. rgn. rewrite br_w0w0. pcn.
  wsx wacc_OpImm F_110 D_fff90913. rgn. rewrite H18, alu_add, zw_add_sext. lits.
  wsx wacc_ShiftImm F_114 D_00395613. rgn. rewrite srl3 by lia.
  wsx wacc_Op F_118 D_00c585b3. rgn. rewrite alu_add, zw_add.
  replace ((E + -1) / 8)%Z with eq8 by (unfold eq8; f_equal; lia).
  wlsh F_11c D_00058583 (K + eq8)%Z Hmat' Hmem.
  wsx wacc_Branch F_120 D_04058263. rgn. rewrite br_w0w0. pcn.
  apply (B5 _ model'0 (0 + 1 + 1)); [ | lia | reflexivity | rgn; exact Hsp2 | rgn; exact H19 | rgn; exact H10 ].
  split; [mfs HF | split; [exact Hmat'0 | lia]].
Qed.
Lemma addzw : forall x (a : word), Z_to_bv 64 x + a = Z_to_bv 64 (bv_unsigned a + x).
Proof. intros x a. rewrite <- (Z_to_bv_u a) at 1. rewrite zw_add. f_equal. lia. Qed.

Lemma div8 : forall q, (8 * q / 8 = q)%Z.
Proof. intros q. rewrite Z.mul_comm. apply Z.div_mul. lia. Qed.

Lemma B3 : forall ms model, BI ms model 0 Mf ->
  ms_pc_val ms = pcw b 0xe8 -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rg ms 8 = beg -> rg ms 18 = Z_to_bv 64 E -> rg ms 20 = Z_to_bv 64 (8 * ae8) -> rg ms 21 = Z_to_bv 64 aK ->
  rg ms 10 = Z_to_bv 64 (K + ab8) -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model (HF & Hmat & Hk0) Hpc Hsp2 H8 H18 H20 H21 H10.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg).
  pose proof ab8_f. pose proof ae8_f.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model 0 Hmat); exact Hh0).
  wsx wacc_OpImm F_e8 D_00050993. rgn. rewrite H10, alu_add, add_sext0.
  wsx wacc_OpImm F_ec D_000a0513. rgn. rewrite H20, alu_add, add_sext0.
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Jal; [ fetch_tac F_f0 | reflexivity | exact D_a85ff0ef ] | apply acc_ok_nil | ].
  pcn.
  apply (h_sum model Hh _ T (8 * ae8)).
  - reflexivity.
  - cbn [ms_pc_val setx]. unfold pcw. f_equal. lia.
  - rgn. reflexivity.
  - destruct Hreg as [HH|HL]; [right | left]; lia.
  - cbn [ms_mem setx]. rewrite Hmem. exact globals_Mf.
  - exact (globals_nl_mat model 0 Hmat).
  - rgn. apply ra_even; lia.
  - intros ms' HFR Hpc' H10'.
    rewrite div8 in H10'.
    pose proof HFR as (_ & _ & _ & _ & _ & _ & GR).
    apply (B4 ms' model 0).
    + split; [|split; [exact Hmat | lia]].
      refine (MF_FR ms0 _ ms' BCLOB HCLOB Mf _ HFR _); [ mfs HF | intros r Hin; cbn in Hin |- *; tauto ].
    + reflexivity.
    + rewrite Hpc'. rgn. reflexivity.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact Hsp2.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H8.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H18.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H21.
    + rewrite GR by (cbn; intuition discriminate). rgn. reflexivity.
    + exact H10'.
Qed.

End Main.
End Rip.
