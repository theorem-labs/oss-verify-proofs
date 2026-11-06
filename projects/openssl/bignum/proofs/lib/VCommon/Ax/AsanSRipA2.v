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

From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanSRipA AsanSRipA1.
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

Lemma F_164 : fetch_word segs (pcw b 0x164) = Some (Z_to_bv 32 0x00a9fa63). Proof. fw. Qed.
Lemma F_168 : fetch_word segs (pcw b 0x168) = Some (Z_to_bv 32 0x413505b3). Proof. fw. Qed.
Lemma F_16c : fetch_word segs (pcw b 0x16c) = Some (Z_to_bv 32 0x00098513). Proof. fw. Qed.
Lemma F_174 : fetch_word segs (pcw b 0x174) = Some (Z_to_bv 32 0xfa050ce3). Proof. fw. Qed.
Lemma F_178 : fetch_word segs (pcw b 0x178) = Some (Z_to_bv 32 0x00000413). Proof. fw. Qed.
Lemma F_17c : fetch_word segs (pcw b 0x17c) = Some (Z_to_bv 32 0x00040513). Proof. fw. Qed.
Lemma F_180 : fetch_word segs (pcw b 0x180) = Some (Z_to_bv 32 0x03813083). Proof. fw. Qed.
Lemma F_184 : fetch_word segs (pcw b 0x184) = Some (Z_to_bv 32 0x03013403). Proof. fw. Qed.
Lemma F_188 : fetch_word segs (pcw b 0x188) = Some (Z_to_bv 32 0x02813483). Proof. fw. Qed.
Lemma F_18c : fetch_word segs (pcw b 0x18c) = Some (Z_to_bv 32 0x02013903). Proof. fw. Qed.
Lemma F_190 : fetch_word segs (pcw b 0x190) = Some (Z_to_bv 32 0x01813983). Proof. fw. Qed.
Lemma F_194 : fetch_word segs (pcw b 0x194) = Some (Z_to_bv 32 0x01013a03). Proof. fw. Qed.
Lemma F_198 : fetch_word segs (pcw b 0x198) = Some (Z_to_bv 32 0x00813a83). Proof. fw. Qed.
Lemma F_19c : fetch_word segs (pcw b 0x19c) = Some (Z_to_bv 32 0x04010113). Proof. fw. Qed.
Lemma F_1a0 : fetch_word segs (pcw b 0x1a0) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.

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

Definition BI (ms : machine_state) (model : Model) (k : Z) (m : word -> option byte) : Prop :=
  MF ms0 ms BCLOB m /\ mat_of model0 model k /\ (0 <= k)%Z.

Lemma MF_FR : forall S0 S S' rs rs' m, MF S0 S rs m -> FR rs' S S' -> (forall r, In r rs' -> In r rs) -> MF S0 S' rs m.
Proof.
  intros S0 S S' rs rs' m (A1 & A2 & A3 & A4 & A5 & A6 & A7) (C1 & C2 & C3 & C4 & C5 & C6 & C7) Hinc.
  split; [exact C1|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [rewrite C5; exact A5|]. split; [|congruence].
  intros r Hr. rewrite C7; [exact (A6 r Hr)|]. intros Hin. exact (Hr (Hinc r Hin)).
Qed.

Lemma hclob_cases : forall r : reg, ~ In r HCLOB -> In r [1; 2; 8; 9; 18; 19; 20; 21] \/ ~ In r BCLOB.
Proof.
  intros r Hr. destruct (in_dec (bv_eq_dec 5) r [1; 2; 8; 9; 18; 19; 20; 21]) as [Hin|Hnin]; [left; exact Hin|].
  right. intros Hbc. change BCLOB with (HCLOB ++ [1; 2; 8; 9; 18; 19; 20; 21]) in Hbc.
  apply in_app_or in Hbc as [X|X]; [exact (Hr X) | exact (Hnin X)].
Qed.

Ltac wld F D o Hsp Hrd Hmat :=
  eapply rzc_acc;
  [ assumption | first [ reflexivity | assumption ]
  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | rgn; rewrite Hsp, zw_add_sext; lits; rewrite ?mem_setx; exact Hrd ]
  | rgn; rewrite Hsp, zw_add_sext; lits; cbn [msz_n]; apply (acc_slot _ _ o Hmat); lia
  | ];
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn; rewrite ld_st8.

Lemma B6 : forall ms model k m, BI ms model k m -> (k <= rpg size)%Z ->
  ms_pc_val ms = pcw b 0x178 -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 56)) 8 = Some (store_bytes SZ8 (rg ms0 1)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 48)) 8 = Some (store_bytes SZ8 (rg ms0 8)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 40)) 8 = Some (store_bytes SZ8 (rg ms0 9)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 32)) 8 = Some (store_bytes SZ8 (rg ms0 18)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 24)) 8 = Some (store_bytes SZ8 (rg ms0 19)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 16)) 8 = Some (store_bytes SZ8 (rg ms0 20)) ->
  rdn segs m (Z_to_bv 64 (SP + -64 + 8)) 8 = Some (store_bytes SZ8 (rg ms0 21)) ->
  (forall x : word, ~ (SP - 72 <= bv_unsigned x < SP)%Z -> m x = ms_mem ms0 x) -> mem_grows (ms_mem ms0) m ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model k m (HF & Hmat & Hk0) Hk Hpc Hsp2 R56 R48 R40 R32 R24 R16 R8 Hout Hgr.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg).
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0).
  rewrite <- Hmem in R56, R48, R40, R32, R24, R16, R8.
  wsx wacc_OpImm F_178 D_00000413. rgn. rewrite alu_add, w0_add_sext. lits.
  wsx wacc_OpImm F_17c D_00040513. rgn. rewrite alu_add, add_sext0.
  wld F_180 D_03813083 56%Z Hsp2 R56 Hmat.
  wld F_184 D_03013403 48%Z Hsp2 R48 Hmat.
  wld F_188 D_02813483 40%Z Hsp2 R40 Hmat.
  wld F_18c D_02013903 32%Z Hsp2 R32 Hmat.
  wld F_190 D_01813983 24%Z Hsp2 R24 Hmat.
  wld F_194 D_01013a03 16%Z Hsp2 R16 Hmat.
  wld F_198 D_00813a83 8%Z Hsp2 R8 Hmat.
  wsx wacc_OpImm F_19c D_04010113. rgn. rewrite Hsp2, alu_add, zw_add_sext. lits.
  replace (SP + -64 + 64)%Z with SP by lia. rewrite Z_to_bv_u.
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Jalr; [ fetch_tac F_1a0 | reflexivity | exact D_00008067 ] | apply acc_ok_nil | ].
  rgn. rewrite ?pc_setx, ret_even by exact Hra.
  apply (HK _ model).
  - split; [reflexivity|]. split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|]. split; [exact HR4|].
    split; [|split; [intros x Hx; cbn [ms_mem setx]; rewrite Hmem; exact (Hout x Hx) | cbn [ms_mem setx]; rewrite Hmem; exact Hgr]].
    intros r Hr. destruct (hclob_cases r Hr) as [Hin|Hnb].
    + cbn in Hin. repeat destruct Hin as [<-|Hin]; try contradiction; rgn; first [reflexivity | exact (eq_sym H2)].
    + rewrite rg_setx_x0. rewrite !rg_setx_other by (intros ->; apply Hnb; memb). apply HR. exact Hnb.
  - reflexivity.
  - rgn. reflexivity.
  - apply (mat_of_mono model0 model k); [exact Hmat | exact Hk].
Qed.
Lemma mat_of_trans : forall m0 m m' k k', mat_of m0 m k -> mat_of m m' k' -> mat_of m0 m' (k + k').
Proof.
  intros m0 m m' k k' [(P & HP) Hu] [(P' & HP') Hu']. split.
  - exists P'. rewrite HP', HP. rewrite with_lazy. apply with_vm_backing_twice.
  - lia.
Qed.

Lemma MF_MF : forall S0 S S' rs rs' m m', MF S0 S rs m -> MF S S' rs' m' -> (forall r, In r rs' -> In r rs) -> MF S0 S' rs m'.
Proof.
  intros S0 S S' rs rs' m m' (A1 & A2 & A3 & A4 & A5 & A6 & A7) (C1 & C2 & C3 & C4 & C5 & C6 & C7) Hinc.
  split; [exact C1|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [destruct C5 as [C5|C5]; [rewrite C5; exact A5 | right; exact C5]|]. split; [|exact C7].
  intros r Hr. rewrite C6; [exact (A6 r Hr)|]. intros Hin. exact (Hr (Hinc r Hin)).
Qed.

Lemma ra_even : forall o, (0 <= o <= 0x1000)%Z -> (o mod 4 = 0)%Z -> (bv_unsigned (pcw b o) mod 2 = 0)%Z.
Proof. intros o Ho Hm. unfold pcw. rewrite bvu_z by lia. lia. Qed.

Local Notation K := 0x7fff8000%Z.
Local Notation E := (bv_unsigned beg + size)%Z.

Definition ab8 : Z := ((bv_unsigned beg + 7) / 8)%Z.
Definition ae8 : Z := ((bv_unsigned beg + size) / 8)%Z.
Definition bq : Z := (bv_unsigned beg / 8)%Z.
Definition eq8 : Z := ((bv_unsigned beg + size - 1) / 8)%Z.

Lemma ab8_f : (B <= 8 * ab8 <= B + 7)%Z.
Proof. unfold ab8. pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.
Lemma ae8_f : (E - 7 <= 8 * ae8 <= E)%Z.
Proof. unfold ae8. pose proof (Z.div_mod E 8 ltac:(lia)). pose proof (Z.mod_pos_bound E 8 ltac:(lia)). lia. Qed.
Lemma bq_f : (B - 7 <= 8 * bq <= B)%Z.
Proof. unfold bq. pose proof (Z.div_mod B 8 ltac:(lia)). pose proof (Z.mod_pos_bound B 8 ltac:(lia)). lia. Qed.
Lemma eq8_f : (E - 8 <= 8 * eq8 <= E - 1)%Z.
Proof. unfold eq8. pose proof (Z.div_mod (E - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (E - 1) 8 ltac:(lia)). lia. Qed.

Lemma shadow_Mf' : forall q, (K + bq <= q <= K + eq8)%Z -> bat segs Mf (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Proof. intros q Hq. apply shadow_Mf. unfold bq, eq8 in Hq. lia. Qed.

Lemma B5 : forall ms model k, BI ms model k Mf -> (0 <= k <= 2)%Z ->
  ms_pc_val ms = pcw b 0x164 -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rg ms 19 = Z_to_bv 64 (K + ab8) -> rg ms 10 = Z_to_bv 64 (K + ae8) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model k (HF & Hmat & Hk0) Hk Hpc Hsp2 H19 H10.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg).
  pose proof ab8_f. pose proof ae8_f. pose proof bq_f. pose proof eq8_f.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model k Hmat); exact Hh0).
  wsx wacc_Branch F_164 D_00a9fa63. rgn. rewrite H19, H10, branch_geu_z by lia.
  destruct (Z.ltb_spec (K + ab8) (K + ae8)) as [Hlt|Hge]; cbn [negb]; pcn.
  -
    wsx wacc_Op F_168 D_413505b3. rgn. rewrite H10, H19, alu_sub, zw_sub.
    wsx wacc_OpImm F_16c D_00098513. rgn. rewrite H19, alu_add, add_sext0.
    assert (HF1 : forall S, MF ms0 S BCLOB Mf -> rg S 2 = Z_to_bv 64 (SP + -64) -> ms_pc_val S = pcw b 0x170 ->
              rg S 10 = Z_to_bv 64 (K + ab8) -> rg S 11 = Z_to_bv 64 (ae8 - ab8) -> ms_svc_pending S = None ->
              realizes_cfg segs cfg (mkCfg S model) T).
    { intros S HS Hs2 HSpc HS10 HS11 HSsvc. pose proof HS as (_ & _ & _ & _ & _ & _ & HSmem).
      destruct (jal_ok_sound _ _ _ _ _ HJz) as (wz & iz & HFz & HEz & HDz & HTz).
      eapply rzc_acc; [ assumption | assumption | eapply wacc_Jal; [ fetch_tac HFz | exact HEz | exact HDz ] | apply acc_ok_nil | ].
      rewrite HSpc. pcn.
      apply (miz_sum segs cfg z HWz _ model T (Z_to_bv 64 (K + ab8)) (ae8 - ab8)).
      + reflexivity.
      + cbn [ms_pc_val setx]. unfold pcw. f_equal. lia.
      + exact Hh.
      + rgn. exact HS10.
      + rgn. rewrite HS11. reflexivity.
      + lia.
      + rewrite bvu_z by lia. lia.
      + intros i Hi. cbn [ms_mem setx]. rewrite HSmem. rewrite zw_add. apply shadow_Mf'. lia.
      + pose proof (proj2 Hmat). rewrite (mat_of_vmmaps model0 model k Hmat). pose proof (rpg_f size). lia.
      + rgn. rewrite Hs2, bvu_z by lia. lia.
      + rgn. rewrite Hs2, bvu_z by lia. cbn [ms_mem setx]. rewrite HSmem.
        replace (SP + -64 - 8)%Z with (SP + -64 + -8)%Z by lia. apply st_slot; [apply Mf_grows | lia].
      + rgn. rewrite Hs2, bvu_z by lia. apply (no_lazy_mat model0 model k); [exact Hmat|]. apply (no_lazy_sub model0 _ _ _ _ HnlS); lia.
      + rgn. rewrite Hs2, !bvu_z by lia. destruct Hdsh; [left | right]; lia.
      + rgn. apply ra_even; lia.
      + intros ms' model' HMF Hpc' H10' Hmat'.
        set (m' := write_to_mem Mf (Z_to_bv 64 (SP - 72)) (store_bytes SZ8 (pcw b 0x174))).
        revert HMF. rgn. rewrite Hs2, bvu_z by lia. cbn [ms_mem setx]. rewrite HSmem.
        replace (SP + -64 - 8)%Z with (SP - 72)%Z by lia. intros HMF. fold m' in HMF.
        assert (HMF2 : MF ms0 ms' BCLOB m').
        { apply (MF_MF ms0 (setx S 1 (pcw b 372) (pcw b (0x170 + bv_signed iz)) (ms_resv S) Mf) ms' BCLOB MZCLOB Mf m');
            [ | exact HMF | intros r Hin; cbn in Hin |- *; tauto ].
          apply MF_setxn; [ exact HS | right; memb | left; reflexivity | symmetry; exact HSmem ]. }
        pose proof HMF2 as (Gsvc & _ & _ & _ & _ & GR & Gmem).
        assert (Hh' : m_halted model' = None) by (rewrite (mat_of_halted model model' _ Hmat'); exact Hh).
        eapply rzc_acc; [ exact Hh' | exact Gsvc
          | eapply wacc_Branch; [ rewrite Hpc'; rgn; exact F_174 | reflexivity | exact D_fa050ce3 ] | apply acc_ok_nil | ].
        rewrite Hpc'. rgn. rewrite H10', (br_eq0 1) by lia. cbn [Z.eqb]. pcn.
        assert (Hm' : forall x : word, ~ (SP - 72 <= bv_unsigned x < SP - 64)%Z -> m' x = Mf x).
        { intros x Hx. unfold m'. apply w2m_outside; rewrite store_bytes8_len, bvu_z by lia; lia. }
        assert (Hrd : forall o, (8 <= o <= 56)%Z -> rdn segs m' (Z_to_bv 64 (SP + -64 + o)) 8 = rdn segs Mf (Z_to_bv 64 (SP + -64 + o)) 8).
        { intros o Ho. apply rdn_ext; rewrite bvu_z by lia; [lia|]. intros x Hx. apply Hm'. lia. }
        apply (B6 _ model' (k + (ae8 - ab8)) m').
        * split; [mfs HMF2 | split; [exact (mat_of_trans model0 model model' k _ Hmat Hmat') | lia]].
        * pose proof (rpg_f size). lia.
        * reflexivity.
        * rgn. pose proof HMF as (_ & _ & _ & _ & _ & HR2' & _).
          rewrite HR2' by (cbn; intuition discriminate). rgn. exact Hs2.
        * rewrite Hrd by lia. exact Mf_read56.
        * rewrite Hrd by lia. exact Mf_read48.
        * rewrite Hrd by lia. exact Mf_read40.
        * rewrite Hrd by lia. exact Mf_read32.
        * rewrite Hrd by lia. exact Mf_read24.
        * rewrite Hrd by lia. exact Mf_read16.
        * rewrite Hrd by lia. exact Mf_read8.
        * intros x Hx. rewrite Hm' by lia. apply Mf_out. lia.
        * apply grows_w. exact Mf_grows. }
    apply HF1; [ mfs HF | rgn; exact Hsp2 | reflexivity | rgn; reflexivity | rgn; f_equal; lia | reflexivity ].
  - apply (B6 _ model k Mf).
    + split; [mfs HF | split; [exact Hmat | exact Hk0]].
    + pose proof (rpg_f size). lia.
    + reflexivity.
    + rgn. exact Hsp2.
    + exact Mf_read56.
    + exact Mf_read48.
    + exact Mf_read40.
    + exact Mf_read32.
    + exact Mf_read24.
    + exact Mf_read16.
    + exact Mf_read8.
    + intros x Hx. apply Mf_out. lia.
    + exact Mf_grows.
Qed.

End Main.
End Rip.
